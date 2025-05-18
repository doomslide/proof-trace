import Lean
import ProofTrace.Data
import ProofTrace.Elab
import ProofTrace.Process
import ProofTrace.Utils
import ProofTrace.Extract
import ProofTrace.Versions

open Lean IO FS System Meta

namespace ProofTrace

def elabAndProcessFile (filePath : System.FilePath) (outPath : System.FilePath) (normModeOpt : Option Meta.TransparencyMode) (mathlibVersion : String) (leanVersion : String) : IO UInt32 := do
  try
    IO.println s!"Elaborating file: {filePath}..."
    let frontendState ← elabFile filePath
    IO.println "Elaboration complete."

    IO.println "Extracting InfoTrees..."
    let infoTrees := frontendState.commandState.infoState.trees
    IO.println s!"Found {infoTrees.size} InfoTrees."

    if infoTrees.isEmpty then
      IO.println "No InfoTrees found. Nothing to process."
      return 0

    IO.println "Extracting final proof states..."
    let finalStateMap ← extractProofStates infoTrees normModeOpt leanVersion mathlibVersion
    IO.println s!"Extracted {finalStateMap.size} final states."

    if finalStateMap.isEmpty then
      IO.println "No final states extracted. Nothing to format."
      return 0

    IO.println "Formatting states into JSON and writing to file..."
    let finalStatesArray : Array FinalGoalState := finalStateMap.toArray.map (·.2)
    processProofs frontendState.commandState.env finalStatesArray outPath
    IO.println "Formatting and writing complete."
    return 0
  catch e =>
    IO.eprintln s!"ERROR processing {filePath}: {e}"
    return 1


def cliMain (rawArgs : List String) : IO UInt32 := do
  -- TODO: Implement better (i.e. less repulsively hacky) argument parsing.
  let args := match rawArgs with
              | "--" :: actualArgs => actualArgs
              | _         => rawArgs
  IO.println s!"ProofTrace CLI invoked with raw args: {rawArgs}, processed args: {args}"
  match args with
  | "fromFile" :: "--src" :: srcPath :: "--out" :: outPath :: restArgs =>
    -- Basic parsing for --norm, assuming it's the only optional arg for now
    let normModeOpt : Option Meta.TransparencyMode :=
      if restArgs.length >= 2 && restArgs.head! == "--norm" then
        match restArgs[1]! with
        | "all" => some .all
        | "default" => some .default
        | "reducible" => some .reducible
        | "instances" => some .instances
        | _ => none
      else
        some .reducible -- Default normalization mode

    let leanVersion := Lean.versionString
    let mathlibVersion ← ProofTrace.findMathlibVersion (← IO.currentDir)

    let normModeStr := match normModeOpt with
    | some .all => "all"
    | some .default => "default"
    | some .reducible => "reducible"
    | some .instances => "instances"
    | none => "none"
    IO.println s!"Command: fromFile, Src: {srcPath}, Out: {outPath}, NormMode: {normModeStr}, Lean: {leanVersion}, Mathlib: {mathlibVersion}"
    elabAndProcessFile (FilePath.mk srcPath) (FilePath.mk outPath) normModeOpt mathlibVersion leanVersion

  | _ =>
    IO.println "Invalid arguments."
    IO.println "Usage:"
    IO.println "  proofTrace fromFile --src <file.lean> --out <output.jsonl> [--norm <mode>]"
    IO.println "  Modes: all, default, reducible, instances"
    return 1

end ProofTrace

-- The actual main entry point for the executable
def main (args : List String) : IO UInt32 :=
  ProofTrace.cliMain args
