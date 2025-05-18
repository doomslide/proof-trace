import Lean
import Lean.Meta
import Std.Data.HashMap
import Std.Data.HashSet
import Lean.Data.Json
import Lean.Exception
import ProofTrace.Data
import ProofTrace.Utils
import ProofTrace.Versions
import Lean.Declaration
import ProofTrace.Primitives
import ProofTrace.Process
import Lean.Environment
import Lean.Elab.Import
import Lean.Util.Paths



open Lean Lean.Meta Std IO FS ProofTrace Lean.Exception ProofTrace.Utils


-- Samples theorems and generates JSONL output
def sampleTheorems (numSamples : Nat) (subLibPrefix : String) (outFile : System.FilePath) : MetaM Unit := do
  liftM <| IO.println s!"Starting 'sampleTheorems' for prefix '{subLibPrefix}', numSamples: {numSamples}"
  let env ← getEnv
  let allModulesInCurrentEnv := env.allImportedModuleNames

  let mut targetModulesFromEnv : HashSet Name := HashSet.emptyWithCapacity 0
  for modName in allModulesInCurrentEnv do
    if subLibPrefix.isPrefixOf modName.toString then
      targetModulesFromEnv := targetModulesFromEnv.insert modName

  liftM <| IO.println s!"'sampleTheorems' sees {targetModulesFromEnv.size} modules in its environment matching prefix '{subLibPrefix}': {targetModulesFromEnv.toArray.map (·.toString)}"

  if targetModulesFromEnv.isEmpty then
    liftM <| IO.println s!"Warning (sampleTheorems): No modules matching prefix '{subLibPrefix}' are loaded in the current environment. No theorems will be sampled."
    return

  let mut targetModuleIndices : HashSet Nat := HashSet.emptyWithCapacity 0
  for modName in targetModulesFromEnv do
    if let some idx := env.getModuleIdx? modName then
      targetModuleIndices := targetModuleIndices.insert idx

  let mut mathlibTheorems : Array Name := #[]
  let constants := env.constants
  for (name, cinfo) in constants.toList do
    if let some modIdx := env.getModuleIdxFor? name then
      if targetModuleIndices.contains modIdx then
        if match cinfo with | .thmInfo _ => true | _ => false then
          mathlibTheorems := mathlibTheorems.push name

  liftM <| IO.println s!"Found {mathlibTheorems.size} potential theorems in target modules."

  if mathlibTheorems.isEmpty then
    liftM <| IO.println "No theorems found in target modules to sample."
    return

  let mut sampledIndices : HashSet Nat := HashSet.emptyWithCapacity numSamples
  let mut sampledNames : Array Name := #[]

  let maxIdx := if mathlibTheorems.size > 0 then mathlibTheorems.size - 1 else 0
  let numToSample := Nat.min numSamples mathlibTheorems.size
  while sampledNames.size < numToSample do
    if maxIdx == 0 && mathlibTheorems.isEmpty then break
    let idx ← liftM <| IO.rand 0 maxIdx
    if !sampledIndices.contains idx then
      if h : idx < mathlibTheorems.size then
        sampledIndices := sampledIndices.insert idx
        sampledNames := sampledNames.push (mathlibTheorems[idx]'h)
      else
         liftM <| IO.println s!"Warning: Generated index {idx} out of bounds {mathlibTheorems.size}"

  liftM <| IO.println s!"Selected {sampledNames.size} unique theorems for processing: {sampledNames}"

  let leanVersion := Lean.versionString
  let mathlibVersion ← liftM <| ProofTrace.findMathlibVersion (← IO.currentDir)

  let mut processedCount := 0
  let mut jsonResults : Array Json := #[]

  for thmName in sampledNames do
    match env.find? thmName with
    | none => liftM <| IO.println s!"Warning: Sampled theorem {thmName} not found in env? Skipping."
    | some cinfo =>
      if let some proofExpr := cinfo.value? then
        try
          let (contextStrings, goalBody) ← ProofTrace.Utils.extractContextGoal cinfo.type
          let mut seeds : NameSet := constsInExpr cinfo.type
          seeds := seeds.union (constsInExpr proofExpr)
          let primitiveNames := primitiveClosure env seeds
          let mut primSpecsData : Array PrimitiveSpecData := #[]
          for primName in primitiveNames.toList do
             match env.find? primName with
             | none => pure ()
             | some primCi =>
               match ← primitiveSpec primCi with
               | some specData => primSpecsData := primSpecsData.push specData
               | none => pure ()
          let primitivesJsonArray ← primSpecsData.mapM primitiveSpecDataToJson
          let primitivesJson := Json.mkObj [("primitives", Json.arr primitivesJsonArray)]
          let goalStr ← pp goalBody
          let proofStr ← pp proofExpr
          let jsonData : JsonSyntheticTheorem := {
            syntheticName := s!"{thmName}_sampled",
            context       := contextStrings,
            goal          := goalStr,
            primitives    := primitivesJson,
            sourceDecl    := thmName.toString,
            proof         := proofStr,
            distractors   := #[],
            prettyProof   := proofStr,
            leanVersion   := leanVersion,
            mathlibVersion:= mathlibVersion,
            originalSource:= "[source extraction not implemented]"
          }
          jsonResults := jsonResults.push (toJson jsonData)
          processedCount := processedCount + 1
        catch e : Lean.Exception =>
          let msgData := e.toMessageData
          let fmt ← msgData.format
          liftM <| IO.println s!"ERROR processing theorem {thmName}: {fmt.pretty}"
      else
        liftM <| IO.println s!"Warning: Theorem {thmName} has no proof value? Skipping."

  liftM <| IO.println s!"Processed {processedCount} theorems. Writing to {outFile}..."
  try
    liftM <| IO.FS.withFile outFile .write fun h => do
      for jsonItem in jsonResults do
        h.putStrLn (jsonItem.compress)
    liftM <| IO.println "Successfully wrote JSONL file."
  catch e : Lean.Exception =>
    let msgData := e.toMessageData
    let fmt ← msgData.format
    liftM <| IO.eprintln s!"ERROR writing output file {outFile}: {fmt.pretty}"


unsafe def discoverAndSampleLogic (numSamples : Nat) (subLibPrefixStr : String) (outFile : System.FilePath) : MetaM UInt32 := do

  let baseImports : Array Lean.Import := #[
    {module := `Init},
    {module := `ProofTrace.Data}, {module := `ProofTrace.Primitives},
    {module := `ProofTrace.Process}, {module := `ProofTrace.Utils},
    {module := `ProofTrace.Versions}
  ]

  let mut effectiveImportsToLoad := baseImports

  -- If the prefix is a Mathlib prefix, ensure Mathlib itself is loaded.
  -- The subLibPrefixStr is still passed to sampleTheorems for finer-grained filtering later.
  if subLibPrefixStr.isPrefixOf "Mathlib" then
    effectiveImportsToLoad := effectiveImportsToLoad.push { module := `Mathlib }
    liftM <| IO.println s!"Prefix '{subLibPrefixStr}' suggests Mathlib. Adding `Mathlib` to imports for loading."
  else
    -- HEURISTIC(!): try loading the first component of the prefix string as a module (this part is particularly YOLO)
    let potentialRootModuleStr := subLibPrefixStr.splitOn "." |>.getD 0 ""
    if !potentialRootModuleStr.isEmpty then
      let potentialRootModuleName := potentialRootModuleStr.toName
      if !potentialRootModuleName.isAnonymous then
        effectiveImportsToLoad := effectiveImportsToLoad.push { module := potentialRootModuleName }
        liftM <| IO.println s!"Attempting to load root module '{potentialRootModuleName}' based on prefix '{subLibPrefixStr}'."
      else
        liftM <| IO.println s!"Could not parse '{potentialRootModuleStr}' from prefix '{subLibPrefixStr}' as a module name to load."
    else
      liftM <| IO.println s!"Prefix '{subLibPrefixStr}' is not a Mathlib prefix and is empty or could not determine a root module to load."

  liftM <| IO.println s!"Module Loading Phase: Attempting to load {effectiveImportsToLoad.size} modules: {effectiveImportsToLoad.map (·.module)}"

  let resultUInt32 : UInt32 ← liftM <| Lean.withImportModules effectiveImportsToLoad Options.empty (trustLevel := 0) fun richEnvForSampling => do
    liftM <| IO.println s!"Module Loading Phase: Successfully created rich environment for sampling with {richEnvForSampling.allImportedModuleNames.size} modules."

    let samplingAction : MetaM Unit := sampleTheorems numSamples subLibPrefixStr outFile

    try
      _ ← ProofTrace.runMetaIO samplingAction richEnvForSampling
      IO.println "withImportModules lambda: sampleTheorems (run via runMetaIO) completed successfully."
      pure (0 : UInt32)
    catch e =>
      IO.eprintln s!"withImportModules lambda: Error from runMetaIO for sampleTheorems: {e}"
      pure (1 : UInt32)

  pure resultUInt32


unsafe def main (rawArgs : List String) : IO UInt32 := do
  let args := match rawArgs with
              | "--" :: actualArgs => actualArgs
              | _         => rawArgs
  IO.println s!"SampleProofs CLI invoked with raw args: {rawArgs}, processed args: {args}"

  match args with
  | [numStr, subLibPrefixStr, outPathStr] =>
    match numStr.toNat? with
    | some numSamples =>
      if numSamples == 0 then do
        IO.eprintln "Number of samples must be positive."
        return 1
      else do
        let outFile := System.FilePath.mk outPathStr
        try
          if let some parentDir := outFile.parent then
            IO.FS.createDirAll parentDir

          initSearchPath (← Lean.findSysroot)
          let initialEnv ← mkEmptyEnvironment

          let result ← ProofTrace.runMetaIO (discoverAndSampleLogic numSamples subLibPrefixStr outFile) initialEnv
          return result
        catch e =>
          IO.eprintln s!"Main try-catch: Execution failed: {toString e}"
          return 1
    | none => do
      IO.eprintln s!"Invalid number of samples: {numStr}"
      return 1
  | _ => do
    IO.eprintln "Usage: lake exe sampleProofs -- <num_samples> <sublibrary_prefix> <output_file.jsonl>"
    IO.eprintln "  Example Prefix: Mathlib.Data.List"
    IO.eprintln "  Example Prefix for local: ProofTrace.Data"
    return 1
