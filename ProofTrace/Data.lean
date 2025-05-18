import Lean
import Lean.Data.Json -- Add import for Json/ToJson
import Lean.Expr -- For Expr
import Lean.Meta.Basic -- For MVarId
import Lean.Meta -- For MetaM
import Lean.PrettyPrinter -- For ppExpr
import Lean.Data.Lsp -- For DocumentUri, Range
import Std.Data.HashMap -- For HashMap
import Std.Data.HashSet -- For HashSet
import Lean.Elab.InfoTree -- For ContextInfo

open Lean
open Std -- Open Std namespace for HashMap and HashSet
open Lean.Elab -- Open Elab namespace for ContextInfo
open Lean.Meta -- For MetaM context needed by constantInfoToJson

namespace ProofTrace


/-- Final structure storing the fully processed and verified goal state information.
    This is produced by Phase 2 (`processStates` in `Extract.lean`) and consumed by
    `formatSyntheticTheorems` in `Process.lean`. -/
structure FinalGoalState where
  goalId    : MVarId
  goalKey   : String       -- Unique key derived from normalized type and minimal lctx
  declName  : Name
  typeExpr  : Expr
  proofExpr : Expr
  lctx      : LocalContext -- Minimal required local context from the original declaration
  leanVersion : String
  mathlibVersion : String
  originalSource : String    -- Optional: source code snippet if available
  deriving Inhabited

/-- Data captured during tactic traversal - tracks goal state at the point a tactic is executed. -/
structure CapturedTacticGoalState where
  mvarId         : MVarId
  goalKey        : String
  declName       : Name
  goalTacticPre  : Expr -- Normalized goal type *before* the tactic
  lctxTactic     : LocalContext -- Filtered LocalContext active *at the tactic node*
  deriving Inhabited

/-- Map from goal keys to goal states captured during traversal. -/
abbrev CapturedGoalMap := HashMap String CapturedTacticGoalState

/-- Map from MVarId to the assignment expression and context where it was found. -/
abbrev AssignmentMap := HashMap MVarId (Expr × ContextInfo)

/-- Combined state for the collection phase - tracks both captured goals and assignments. -/
structure CollectionState where
  capturedGoals  : CapturedGoalMap := {}
  assignments    : AssignmentMap := {}
  potentialGoals : HashSet MVarId := {}
  deriving Inhabited

-- Represents the final data structure for JSON serialization: a synthetic theorem
structure JsonSyntheticTheorem where
  syntheticName : String
  context       : Array String
  goal          : String
  primitives    : Json
  sourceDecl    : String
  proof         : String
  prettyProof   : String
  leanVersion   : String
  mathlibVersion: String
  originalSource: String
  deriving ToJson

-- Represents serializable information from ConstantInfo
structure JsonConstantInfo where
  name : String
  type : String
  value? : Option String -- Only for definitions/theorems
  kind : String -- e.g., "definition", "theorem", "axiom", "inductive", etc.
  deriving ToJson

-- Intermediate data structure for primitive constant info before JSON formatting
structure PrimitiveSpecData where
  name : Name
  type : Expr
  kind : String
  value? : Option Expr := none
  ctors? : Option (List Name) := none
  deriving Inhabited
end ProofTrace
