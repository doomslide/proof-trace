import Lean
import Lean.Meta -- For MetaM, ConstantInfo, getConstInfo?, whnfR
import Lean.Environment -- For Environment, find?, getModuleIdxFor?
import Lean.Util.FoldConsts -- For getUsedConstantsAsSet
import ProofTrace.Utils -- For pp
import ProofTrace.Data -- Import PrimitiveSpecData

open Lean Lean.Meta NameSet

namespace ProofTrace


/-! ## Primitive Constant Identification (Module-Based) -/

/-- `true` if the constant was **imported** from a module whose name
    starts with `Init` or `Prelude`. Works for `Nat`, `Eq`, `Add`, … as well
    as `Init.Data.Nat.Basic.add_comm`. -/
@[inline] def inPrelude? (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | none      => c.getRoot == `Init -- Fallback: If no index, check if root is Init (catches some kernel builtins?)
  | some idx  =>
    -- Ensure modIdx is within bounds before accessing moduleNames
    if h : idx.toNat < env.header.moduleNames.size then
      let modName := env.header.moduleNames[idx.toNat] -- Use h for proof
      modName.getRoot == `Init || modName.getRoot == `Prelude -- Check root namespace
    else
      false -- Index out of bounds, treat as non-primitive

/-! ## Dependency Analysis Helpers -/

/-- Constants (primitive *and* user) that occur syntactically in `e`. -/
@[inline] def constsInExpr (e : Expr) : NameSet :=
  e.getUsedConstantsAsSet

/-- Constants that occur in a declaration's type **or** value. -/
@[inline] def depsOfConst (ci : ConstantInfo) : NameSet :=
  ci.getUsedConstantsAsSet

/-- Good constructor = constructor *and* its inductive is in the prelude. -/
@[inline] def goodCtor? (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.ctorInfo ctorVal) =>
      -- Check if the inductive type is in the prelude
      inPrelude? env ctorVal.induct
  | _ => false -- Not a constructor or not found

/-- Check if a ConstantInfo corresponds to an implementation detail definition. -/
@[inline] def implementationDetail? (ci : ConstantInfo) : Bool :=
  match ci with
  -- Check for abbrev
  | .defnInfo d => d.hints.isAbbrev
  | _          => false

/-- Keep only constants that are in the prelude and are NOT implementation details. -/
@[inline] def keepPrimitive (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | none    => false -- Constant not found
  | some ci => (inPrelude? env n) && !implementationDetail? ci

/-! ## Primitive Closure Computation -/

/-- Minimal set of *prelude* constants (excluding implementation details) reachable from `seeds`. -/
def primitiveClosure (env : Environment) (seeds : NameSet) : NameSet := Id.run do
  -- Use the recursive helper function with the new keepPrimitive check and fuel
  let rec go (fuel : Nat) (todo : List Name) (acc : NameSet) : NameSet :=
    match fuel with
    | 0 => acc -- Ran out of fuel, return what we have
    | fuel' + 1 =>
      match todo with
      | []       => acc
      | n :: ns  =>
        if acc.contains n then
          go fuel' ns acc
        else
          -- Add to accumulator *if* we should keep it
          let acc' := if keepPrimitive env n then acc.insert n else acc -- Use keepPrimitive
          -- Find direct dependencies of the current constant
          let more : NameSet := match env.find? n with
            | some ci => ci.getUsedConstantsAsSet
            | none    => {}
          -- Filter dependencies already in acc'
          let new_todos := (more.toList.filter (λ dep => !acc'.contains dep))
          go fuel' (new_todos ++ ns) acc' -- Spend secondary fuel
  -- Start the recursion with initial seeds and initial fuel
  let initialFuel := seeds.size * 10 + 1000
  go initialFuel seeds.toList {}

/-! ## Primitive Spec Generation -/

private def getConstKindStr (c : ConstantInfo) : String := match c with
    | .axiomInfo   _ => "axiom"
    | .defnInfo    _ => "definition"
    | .thmInfo     _ => "theorem"
    | .opaqueInfo  _ => "opaque"
    | .quotInfo    _ => "quotient"
    | .inductInfo  _ => "inductive"
    | .ctorInfo    _ => "constructor"
    | .recInfo     _ => "recursor"

/-- Convert a primitive constant into a structured data. -/
def primitiveSpec (ci : ConstantInfo) : MetaM (Option PrimitiveSpecData) := do
  match ci with
  | .inductInfo i =>
      return some {
        name   := i.name,
        type   := i.type,
        kind   := "inductive",
        ctors? := i.ctors -- Store constructor names
      }

  | .ctorInfo _ => return none

  | .recInfo _ => return none

  | .defnInfo d =>
      -- expose one *unfolded* definition (use whnfR for less reduction)
      let rhs ← try whnfR d.value catch _ => pure d.value
      return some {
        name   := d.name,
        type   := d.type,
        kind   := "definition",
        value? := rhs
      }

  | _ =>
      -- axioms, theorems, opaque defs etc.
      return some {
        name   := ci.name,
        type   := ci.type,
        kind   := getConstKindStr ci
      }


end ProofTrace
