import Lean
import Lean.Data.Json
import Lean.Meta
import ProofTrace.Data
import ProofTrace.Utils
import ProofTrace.Primitives
import Lean.Log

open Lean Lean.Meta Json NameSet
namespace ProofTrace

/-- Helper function to check if a name is an instance. -/
def isInstanceName (env : Environment) (name : Name) : Bool :=
  let state := Lean.Meta.instanceExtension.getState env
  state.instanceNames.contains name

def primitiveSpecDataToJson (specData : PrimitiveSpecData) : MetaM Json := do
  let env ← getEnv
  let typeStr ← pp specData.type
  let mut fields : List (String × Json) := [
    ("name", toJson specData.name.toString),
    ("type", toJson typeStr),
    ("kind", toJson specData.kind)
  ]

  if let some val := specData.value? then
    fields := ("value", toJson (← pp val)) :: fields

  if let some ctorNames := specData.ctors? then
    let ctorSigs ← ctorNames.mapM fun ctorName => do
      match env.find? ctorName with
      | some (.ctorInfo ctorVal) =>
          pure <| Json.mkObj [("name", toJson ctorName.toString), ("type", toJson (← pp ctorVal.type))]
      | _ => pure <| Json.mkObj [("name", toJson s!"{ctorName}_NotFound"), ("type", Json.null)]
    fields := ("ctors", Json.arr ctorSigs.toArray) :: fields

  return Json.mkObj fields

/- Format a single FinalGoalState into a JsonSyntheticTheorem object. -/
def formatSyntheticTheorem (state : FinalGoalState) : MetaM Json := do
  -- Get Environment once inside MetaM
  let env ← getEnv

  -- 1. Collect seeds from the goal state (type, proof, context)
  let mut seeds : NameSet := constsInExpr state.typeExpr
  seeds := seeds.union (constsInExpr state.proofExpr)
  for ldecl in state.lctx do
    seeds := seeds.union (constsInExpr ldecl.type)
    if let some val := ldecl.value? then
        seeds := seeds.union (constsInExpr val)

  -- 2. Compute the primitive closure
  let primitiveNames := primitiveClosure env seeds

  -- 3. Get PrimitiveSpecData for each primitive
  let mut primSpecsData : Array PrimitiveSpecData := #[]
  for primName in primitiveNames.toList do
    match env.find? primName with
    | none =>
        logWarning m!"Primitive constant {primName} not found in environment, skipping."
    | some ci =>
        -- Call the updated primitiveSpec (without env)
        match ← primitiveSpec ci with
        | some specData => primSpecsData := primSpecsData.push specData
        | none => pure () -- Skip kinds that return none (ctors, recursors)

  -- 4. Convert PrimitiveSpecData array to Json
  let primitivesJsonArray ← primSpecsData.mapM primitiveSpecDataToJson

  -- Create `primitives` JSON object
  let primitivesJson := Json.mkObj [
    ("primitives", Json.arr primitivesJsonArray)
  ]

  -- 5. Pretty print other components
  let contextStrings ← lctxToString state.lctx
  let goalStr ← ppExprWithCtx state.lctx #[] state.typeExpr
  let proofStr ← ppExprWithCtx state.lctx #[] state.proofExpr
  let distractorsStr : Array String := #[] -- Placeholder

  -- 6. Construct JsonSyntheticTheorem
  let jsonData : JsonSyntheticTheorem := {
      syntheticName := s!"{state.declName}_goal_{state.goalKey}",
      context       := contextStrings,
      goal          := goalStr,
      primitives    := primitivesJson,
      sourceDecl    := state.declName.toString,
      proof         := proofStr,
      distractors   := distractorsStr,
      prettyProof   := proofStr,
      leanVersion   := state.leanVersion,
      mathlibVersion:= state.mathlibVersion,
      originalSource:= state.originalSource
    }

  -- 7. Convert to Json
  pure (toJson jsonData)

/-- Take an array of FinalGoalStates, format them to JSON, and write to a file. -/
def processProofs (env : Environment) (states : Array FinalGoalState) (out : System.FilePath) : IO Unit := do
  IO.println s!"Processing {states.size} final states for JSON output..."
  let successfulCountRef ← IO.mkRef (0 : Nat)

  IO.FS.withFile out .write fun h => do -- Use .write to overwrite
    for state in states do
      try
        let json ← runMetaIO (formatSyntheticTheorem state) env

        h.putStrLn (json.compress)
        successfulCountRef.modify (· + 1)

        let count ← successfulCountRef.get
        if count % 10 == 0 then
            IO.println s!"  ..processed {count}/{states.size}"

      catch e =>
        IO.eprintln s!"ERROR processing state from decl {state.declName} (key {state.goalKey}): {e}"

  let finalCount ← successfulCountRef.get
  IO.println s!"Successfully processed and wrote {finalCount}/{states.size} states to {out}."

end ProofTrace
