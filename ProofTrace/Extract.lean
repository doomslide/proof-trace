import Lean
import Lean.Meta
import Lean.Elab.InfoTree
import Lean.Server.Snapshots
import Std.Data.HashMap
import Lean.Meta.CollectFVars
import Lean.Meta.Reduce
import Std.Data.HashSet
import Lean.Log
import Init.Control.State

import ProofTrace.Data
import ProofTrace.Utils

namespace ProofTrace

open Lean Lean.Elab Lean.Meta Std

/-!
# Proof State Extraction

This module extracts self contained goal states in two steps:

**Step 1: Collection**
- Traverses the resolved `InfoTree`.
- Captures goal states at tactic nodes with their contexts.
- Records MVarIds encountered.
- Identifies MVarId assignments and the contexts where they were assigned.

**Step 2: Processing**
- Links captured goal states with their assignments.
- For each captured goal with an assignment, verifies the assignment and creates a final goal state.
-/

/-- The final output map, keyed by the unique `goalKey`. -/
abbrev FinalResultMap := HashMap String FinalGoalState

/-- Placeholder expression for abstracting unresolved metavariables (Should never happen?) -/
@[match_pattern] def abstractedMVarPlaceholder : Expr :=
  mkApp (mkConst `sorryAx [levelZero]) (mkConst `False)

/-- Replace remaining Expr.mvar nodes in an expression with a placeholder. -/
partial def abstractMVars (e : Expr) : MetaM Expr := do
  -- Use transform to visit each subexpression
  Core.transform e (post := fun subExpr => do
    -- After visiting children, check if the current subExpr is an mvar
    match subExpr with
    | .mvar mvarId =>
        -- Check if it's *still* assigned in the current context (should not happen after instantiateMVars, but check anyway)
        let assignment? ← getExprMVarAssignment? mvarId
        if assignment?.isNone then
            -- It's an unassigned mvar, replace it
            return .done abstractedMVarPlaceholder
        else
            -- It was assigned, keep the assigned value (instantiateMVars should handle this ideally...)
            return .continue subExpr
    | _ => return .continue subExpr
  )

/-- Apply abstractMVars to the type and value (if present) of a LocalDecl. -/
def abstractMVarsLocalDecl (decl : LocalDecl) : MetaM LocalDecl := do
  try
    match decl with
    | .cdecl index fvarId userName type bi kind =>
        let abstractedType ← try
          abstractMVars type
        catch e =>
          logInfo m!"Minor error during type abstraction for {decl.userName}, using original: {e.toMessageData}"
          pure type
        return .cdecl index fvarId userName abstractedType bi kind
    | .ldecl index fvarId userName type value nonDep kind =>
        let abstractedType ← try
          abstractMVars type
        catch e =>
          logInfo m!"Minor error during type abstraction for {decl.userName}, using original: {e.toMessageData}"
          pure type
        let abstractedValue ← try
          abstractMVars value
        catch e =>
          logInfo m!"Minor error during value abstraction for {decl.userName}, using original: {e.toMessageData}"
          pure value
        return .ldecl index fvarId userName abstractedType abstractedValue nonDep kind
  catch e =>
    -- Only catch unexpected errors\
    logWarning m!"Failed to abstract declaration {decl.userName}: {e.toMessageData}"
    return decl

/-- Apply abstractMVarsLocalDecl to all declarations in a LocalContext -/
def abstractMVarsLCtx (lctx : LocalContext) : MetaM LocalContext := do
  -- Only log in trace mode
  if (← getOptions).getBool `trace.prooftrace.context false then
    let declNames := lctx.foldl (init := #[]) fun acc decl => acc.push decl.userName
    logInfo m!"Original lctx has {declNames.size} declarations: {declNames}"

  -- Build a new context from all declarations
  let declsArray := lctx.foldl (init := #[]) fun acc decl => acc.push decl
  let abstractedDecls ← declsArray.mapM abstractMVarsLocalDecl
  let mut resultLCtx := LocalContext.empty
  for decl in abstractedDecls do
    resultLCtx := resultLCtx.addDecl decl
  -- Only log in trace mode
  if (← getOptions).getBool `trace.prooftrace.context false then
    let resultNames := resultLCtx.foldl (init := #[]) fun acc decl => acc.push decl.userName
    logInfo m!"Result lctx has {resultNames.size} declarations: {resultNames}"
  return resultLCtx

/-! ## Helper Functions -/

/-- Generate an efficient key from an expression and context using hashing. -/
def generateGoalKey (expr : Expr) (lctx : LocalContext) : MetaM String := do
  let contextData := lctx.foldl (init := #[]) fun acc decl =>
    if decl.isImplementationDetail then acc else acc.push (decl.userName, decl.type, decl.value?)
  -- Hash the expression and the context data together
  let combinedHash := hash (expr, contextData)
  return s!"goal_{combinedHash}"

/-- Captures goal state at a tactic node. -/
def captureGoalState (mvarId : MVarId) (ctx : ContextInfo) (normMode : Option TransparencyMode) : MetaM (Option (String × CapturedTacticGoalState)) := do
  try
    -- Get the goal declaration info
    let decl ← Lean.MVarId.getDecl mvarId
    let rawLCtx := decl.lctx

    -- Instantiate metavariables in the local context
    let mut instLCtx := LocalContext.empty
    for d in rawLCtx do
      let instTypeDecl ← instantiateMVars d.type
      match d with
      | .cdecl idx fid userName _ bi kind =>
          instLCtx := instLCtx.addDecl (LocalDecl.cdecl idx fid userName instTypeDecl bi kind)
      | .ldecl idx fid userName _ val nonDep kind =>
          let instVal ← instantiateMVars val
          instLCtx := instLCtx.addDecl (LocalDecl.ldecl idx fid userName instTypeDecl instVal nonDep kind)

    -- Instantiate goal type and normalize
    let instType ← instantiateMVars decl.type
    let normGoalType ← normalize instType normMode

    -- Generate a key for the goal
    let key ← generateGoalKey normGoalType instLCtx

    -- Get the declaration name from context
    let declName := ctx.parentDecl?.getD `_unknown_decl

    -- Create the CapturedTacticGoalState with instantiated context
    let capturedState : CapturedTacticGoalState := {
      mvarId := mvarId,
      goalKey := key,
      declName := declName,
      goalTacticPre := normGoalType,
      lctxTactic := instLCtx
    }

    return some (key, capturedState)
  catch e =>
    logWarning m!"Failed to capture goal state for mvar {mvarId}: {e.toMessageData}"
    return none

/-- Internal stateful computation for collecting data. -/
partial def collectDataM (trees : PersistentArray InfoTree) (normMode : Option TransparencyMode) : StateT CollectionState IO Unit := do
  let rec collectGoals (ti : TacticInfo) (ctx : ContextInfo) : StateT CollectionState IO Unit := do
    for mvarId in ti.goalsBefore do
      modify fun state => { state with potentialGoals := state.potentialGoals.insert mvarId }
      -- Run MetaM action and handle result within IO, then lift to StateT
      let captureResult : Option (String × CapturedTacticGoalState) ← liftM <| (do
        match ← (ctx.runMetaM {} (captureGoalState mvarId ctx normMode)).toIO' with
        | Except.ok maybeResult => pure maybeResult
        | Except.error e =>
            IO.println s!"[ProofTrace.Extract.collectGoals] Warning: Error running captureGoalState for mvar {mvarId.name}: {toString e}"
            pure none
        : IO _)
      -- Update capturedGoals if capture succeeded and key is new
      if let some (key, capturedState) := captureResult then
        modify fun state =>
          if state.capturedGoals.contains key then
            state -- Key already exists, no change
          else
            { state with capturedGoals := state.capturedGoals.insert key capturedState }

    -- Also track goals in goalsAfter
    for mvarId in ti.goalsAfter do
      modify fun state => { state with potentialGoals := state.potentialGoals.insert mvarId }

  let rec checkAssignments (ctx : ContextInfo) : StateT CollectionState IO Unit := do
    let mctx := ctx.mctx
    let currentAssignments ← get <&> (·.assignments)
    let newAssignments := mctx.eAssignment.foldl (init := currentAssignments) fun assignments mvarId assignedExpr =>
        if !assignedExpr.isMVar then
          assignments.insert mvarId (assignedExpr, ctx)
        else
          assignments
    modify fun state => { state with assignments := newAssignments }

  -- Recursive traversal of an InfoTree
  let rec process (tree : InfoTree) (ctx? : Option ContextInfo) : StateT CollectionState IO Unit := do
    match tree with
    | InfoTree.context partialCtxNode t =>
        let mergedCtx? := partialCtxNode.mergeIntoOuter? ctx?
        match mergedCtx? with
        | none => process t none
        | some ctx =>
            checkAssignments ctx
            process t mergedCtx?

    | InfoTree.node info children =>
        -- Process tactic nodes
        match info, ctx? with
        | .ofTacticInfo ti, some ctx => collectGoals ti ctx
        | _, _ => pure ()

        -- Process children with updated context
        let nodeCtx? := Info.updateContext? ctx? info
        for child in children do
          process child nodeCtx?

        -- Check assignments after processing children
        match nodeCtx? with
        | some ctx => checkAssignments ctx
        | none => pure ()

    | InfoTree.hole mvarId =>
        -- Update potentialGoals
        modify fun state => { state with potentialGoals := state.potentialGoals.insert mvarId }

  for tree in trees do
    process tree none

  pure ()

/-- Process the InfoTree to collect tactic goals and assignments using StateT. -/
def collectData (trees : PersistentArray InfoTree) (normMode : Option TransparencyMode) : IO CollectionState := do
  -- Run the StateT computation, starting with an empty CollectionState
  let (_, finalState) ← collectDataM trees normMode |>.run {}
  return finalState

-- Helper function to convert TransparencyMode to String - MARKED PRIVATE
private def transparencyModeToString (mode : TransparencyMode) : String :=
  match mode with
  | .all => "all"
  | .default => "default"
  | .reducible => "reducible"
  | .instances => "instances"

/-- Process the collected state to generate verified FinalGoalStates. -/
def processCollectedData (state : CollectionState)
                       (normMode : Option TransparencyMode := some .reducible)
                       (leanVersion : String) (mathlibVersion : String) : IO FinalResultMap := do
  let mut results : FinalResultMap := {}

  -- Debug output
  let normModeStr := match normMode with | some m => transparencyModeToString m | none => "none"
  -- Revert this specific message back to IO.println for now
  IO.println s!"[processCollectedData] Using normalization mode: {normModeStr}"

  -- Extract the maps from the collection state
  let capturedGoals := state.capturedGoals
  let assignments := state.assignments

  -- Process each captured goal
  for (goalKey, capturedState) in capturedGoals.toList do
    let mvarId := capturedState.mvarId

    -- Try to find the assignment
    match assignments.get? mvarId with
    | some (finalExpr, solveCtx) =>
        -- Define the MetaM task to analyze the goal and proof.
        let analysisTask : MetaM (Option FinalGoalState) := do
          let normModeStr := match normMode with | some m => transparencyModeToString m | none => "none"
          logInfo m!"Processing goal: {goalKey} with normMode: {normModeStr}"

          let originalSource := "[source extraction not implemented]"

          -- 1. Zeta Reduce the assigned expression.
          let zetaReducedProof ← Meta.zetaReduce finalExpr

          -- Enter the context where the goal was originally captured (lctxTactic)
          withLCtx capturedState.lctxTactic {} do
            -- 2. Normalize the proof expression using the chosen mode
            let normModeStr := match normMode with | some m => transparencyModeToString m | none => "none"
            logInfo m!"About to normalize proof expression with mode: {normModeStr}"
            let normProofExprBase ← normalize zetaReducedProof normMode
            let normGoalTypeBase := capturedState.goalTacticPre

            -- 3. Verify type match
            let proofType ← inferType normProofExprBase
            unless ← isDefEq proofType normGoalTypeBase do
              logWarning m!"Type mismatch for {goalKey}:\nProof Type: {← ppExpr proofType}\nGoal Type: {← ppExpr normGoalTypeBase}"
              return none

            -- 4. Abstraction step
            let normGoalType ← abstractMVars normGoalTypeBase
            let normProofExpr ← abstractMVars normProofExprBase
            let finalMinLCtx ← abstractMVarsLCtx capturedState.lctxTactic

            -- 5. Create final state
            let finalState : FinalGoalState := {
              goalId := mvarId,
              goalKey := goalKey,
              declName := capturedState.declName,
              typeExpr := normGoalType,
              proofExpr := normProofExpr,
              lctx := finalMinLCtx,
              leanVersion := leanVersion,
              mathlibVersion := mathlibVersion,
              originalSource := originalSource
            }
            return some finalState

        -- Execute the analysis task using the solveCtx (provides env/options).
        match ← runMetaIO analysisTask solveCtx.env solveCtx.options with
        | some finalState =>
            results := results.insert goalKey finalState
        | none => pure () -- MetaM action returned none or runner failed

    | none => pure () -- No assignment found for this captured goal

  return results

/-- Main extraction function - collects and processes proof states from InfoTrees. -/
def extractProofStates (infoTrees : PersistentArray InfoTree)
                      (normMode : Option TransparencyMode := some .reducible)
                      (leanVersion : String) (mathlibVersion : String) : IO FinalResultMap := do
  -- Step 1: Collect data from InfoTrees
  IO.println "[extractProofStates] Step 1: Collecting goal states and assignments..."
  let collectionState ← collectData infoTrees normMode
  IO.println s!"[extractProofStates] Found {collectionState.potentialGoals.size} potential goals, {collectionState.capturedGoals.size} captured states, {collectionState.assignments.size} assignments."
  -- Step 2: Process collected data
  IO.println "[extractProofStates] Step 2: Processing collected data..."
  let finalResults ← processCollectedData collectionState normMode leanVersion mathlibVersion
  IO.println s!"[extractProofStates] Extracted {finalResults.size} verified final goal states."
  return finalResults

end ProofTrace
