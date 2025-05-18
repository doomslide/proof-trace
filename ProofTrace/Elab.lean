import Lean
import Lean.Elab.Frontend
import Lean.Elab.Import -- For processHeader, headerToImports, importModules
import Lean.Parser -- For parseHeader, InputContext
import Lean.Util.Paths -- For initSearchPath, findSysroot, modPathToCoreName
import Lean.Util.FileSetupInfo -- Add this for FileSetupInfo
import Lean.LoadDynlib -- Add this for loadDynlib
import Lean.Elab.InfoTree
import Lean.Server.Snapshots -- Required for Snapshot type
import Std.Data.HashMap -- Required for HashMap used in Extract

import ProofTrace.Data -- Import local data structures (FinalGoalState)
import ProofTrace.Extract -- Import the consolidated extraction logic
import ProofTrace.Utils -- Import helpers

open Lean Lean.Elab Lean.Elab.InfoTree Lean.Meta Std IO FS System

namespace ProofTrace

/-! ## 4 Front-end driver: elaborate a file and fetch the trees -/

/-- Elaborate a Lean file, processing imports and commands to collect InfoTrees.
    Uses `lake setup-file` to determine search paths and options. -/
def elabFile (file : System.FilePath) : IO Frontend.State := do
  -- 1. Read file and parse header early to get imports
  let src ← IO.FS.readFile file
  let ictx := Parser.mkInputContext src file.toString
  let (header, parserState, messages0) ← Parser.parseHeader ictx
  let imports := Elab.headerToImports header

  -- 2. Define Lake path (assume it's in PATH)
  let lakePathStr := "lake"

  -- 3. Run `lake setup-file`
  let lakeOutput ← IO.Process.output {
    cmd := lakePathStr,
    args := #["setup-file", file.toString] ++ imports.map (toString ·.module),
  }

  -- 4. Process Lake output
  if lakeOutput.exitCode != 0 then
    IO.eprintln s!"ERROR [elabFile]: `lake setup-file` failed for {file}."
    IO.eprintln s!"Stderr:\n{lakeOutput.stderr}"
    throw <| IO.userError s!"`lake setup-file {file}` failed (see stderr above)."

  let fileSetupInfo ← match Json.parse lakeOutput.stdout >>= fromJson? (α := FileSetupInfo) with
    | Except.ok info => pure info
    | Except.error e => throw <| IO.userError s!"Invalid JSON output from `lake setup-file`:\n{e}\nstdout:\n{lakeOutput.stdout}"

  -- 5. Initialize Lean Environment based on Lake info
  Lean.initSearchPath (← Lean.findSysroot)
  searchPathRef.modify fun currentSearchPath => currentSearchPath ++ fileSetupInfo.paths.oleanPath

  discard <| fileSetupInfo.paths.loadDynlibPaths.mapM loadDynlib

  let opts := fileSetupInfo.setupOptions.toOptions
  let trustLevel : UInt32 := 1024

  let env0 ← importModules (loadExts := true) imports opts trustLevel

  -- Check for errors after importing modules
  if messages0.hasErrors then -- Check initial parse messages too
    IO.eprintln s!"ERROR [elabFile]: Errors found after header parse/import for {file}:"
    for msg in messages0.toList do IO.eprintln (← msg.toString)
    throw <| IO.userError s!"Errors occurred during header processing or import resolution for {file}."

  -- 7. Run the rest of the file
  let mainModuleName : Name := `_ProofTraceRun -- Dummy name
  let env0 := env0.setMainModule mainModuleName
  let commandState := Command.mkState env0 messages0 opts -- Use potentially updated messages and final options

  let finalFrontendState ← IO.processCommands ictx parserState commandState

  -- Check for errors during command processing
  if finalFrontendState.commandState.messages.hasErrors then
    IO.eprintln s!"ERROR [elabFile]: Errors found after command processing for {file}:"
    for msg in finalFrontendState.commandState.messages.toList do IO.eprintln (← msg.toString)
    -- Don't throw error here, allow extraction attempt anyway?
    -- throw <| IO.userError s!"Errors occurred during command processing for {file}."
    IO.eprintln s!"Warning: Errors occurred during command processing for {file}, extraction may be incomplete."

  return finalFrontendState

end ProofTrace
