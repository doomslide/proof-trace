import Lean
import Lean.Meta
import Lean.Log
import ProofTrace.Data

open Lean Lean.Meta IO ProofTrace

namespace ProofTrace

/-- `normalize` normalizes an expression `e` according to the given `Option TransparencyMode`.
    Uses Lean's `whnf` with specified transparency -/
def normalize (e : Expr) (mode : Option TransparencyMode := some .reducible) : MetaM Expr := do
  let e ← instantiateMVars e
  match mode with
  | none        => pure e
  | some tr => withTransparency tr (whnf e)

/-- Pretty-print an expression to `String`. -/
def pp (e : Expr) : MetaM String := return (← PrettyPrinter.ppExpr e).pretty

/-- Pretty-print an expression `e` *as if we were still inside* the
    local context `lctx` with local instances `linsts`. -/
def ppExprWithCtx
    (lctx   : LocalContext)
    (linsts : LocalInstances := #[])
    (e      : Expr) : MetaM String := do
  withLCtx lctx linsts <| do
    let fmt ← Lean.PrettyPrinter.ppExpr e
    pure fmt.pretty

def lctxToString (lctx : LocalContext) : MetaM (Array String) :=
  lctx.foldlM (init := #[]) fun acc decl => do
    if decl.isImplementationDetail then return acc
    -- Use ppExprWithCtx here, passing the *full context* being iterated over
    let typeStr ← ppExprWithCtx lctx #[] decl.type
    let currentLine := s!"({decl.userName} : {typeStr})"
    return acc.push currentLine

/-- Simplified `runMetaIO` using standard Lean runners.
    Assumes logging (Info, Warning, Error) happens *within* the `MetaM` action `x`.
    Propagates errors as IO exceptions. -/
def runMetaIO {α} (x : MetaM α) (env : Environment) (opts : Options := {}) : IO α := do
  -- Contexts and States needed for run'
  let coreCtx : Core.Context := { options := opts, fileName := "<runMetaIO>", fileMap := default }
  let coreState : Core.State := { env := env }
  let metaCtx : Meta.Context := {}
  let metaState : Meta.State := {}

  -- Run MetaM -> CoreM -> EIO
  let eioAction : EIO Exception α := (MetaM.run' x metaCtx metaState).run' coreCtx coreState

  match ← EIO.toIO' eioAction with
  | Except.ok a => pure a
  | Except.error e =>
      let errorMsg ← e.toMessageData.toString
      IO.eprintln s!"Error in runMetaIO: {errorMsg}"
      throw <| IO.Error.userError s!"runMetaIO failed: {errorMsg}"


/-! ## ConstantInfo to JSON Conversion -/

def constantInfoToJson (ci : ConstantInfo) : MetaM Json := do
  let kind := match ci with
    | .axiomInfo   _ => "axiom"
    | .defnInfo    _ => "definition"
    | .thmInfo     _ => "theorem"
    | .opaqueInfo  _ => "opaque"
    | .quotInfo    _ => "quotient"
    | .inductInfo  _ => "inductive"
    | .ctorInfo    _ => "constructor"
    | .recInfo     _ => "recursor"
  -- Use snake_case for local json variable
  let json_info : JsonConstantInfo := {
    name   := ci.name.toString,
    type   := (← PrettyPrinter.ppExpr ci.type).pretty,
    value? := ← ci.value?.mapM (fun v => return (← PrettyPrinter.ppExpr v).pretty),
    kind   := kind
  }
  return toJson json_info

namespace Utils

def extractContextGoal (typeExpr : Expr) : MetaM ((Array String) × Expr) := do
  forallTelescope typeExpr fun fvars body => do
    let lctx ← getLCtx
    let ctxStrings ← fvars.mapM fun fvar => do
      let decl ← fvar.fvarId!.getDecl
      -- ppExprWithCtx is in the outer ProofTrace namespace, call it qualified
      let typeStr ← ProofTrace.ppExprWithCtx lctx #[] decl.type
      pure s!"({decl.userName} : {typeStr})"
    return (ctxStrings, body)

end Utils

end ProofTrace
