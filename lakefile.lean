import Lake
open Lake DSL
open Lean System

package «ProofTrace» where

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"
require batteries from git "https://github.com/leanprover-community/batteries" @ "main"
lean_lib «ProofTrace» where
  roots := #[`ProofTrace.Data, `ProofTrace.Utils, `ProofTrace.Primitives, `ProofTrace.Extract, `ProofTrace.Elab, `ProofTrace.Process, `ProofTrace.Versions]
  precompileModules := true

@[default_target]
lean_exe «proofTrace» where
  root := `ProofTrace.Main
  supportInterpreter := true

-- Executable target for SampleFromPrefix.lean
lean_exe «sampleProofs» where
  root := `scripts.SampleFromPrefix
  supportInterpreter := true
  extraDepTargets := #[`ProofTrace]
