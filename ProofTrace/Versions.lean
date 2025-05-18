import Lean
import Lean.Data.Json
import Init.System.FilePath

namespace ProofTrace

def findMathlibVersion (rootDir : System.FilePath) : IO String := do
  let manifestPath1 := rootDir / "lake-manifest.json"
  let manifestPath2 := rootDir.parent.getD rootDir / "lake-manifest.json"

  let manifestPathOpt : Option System.FilePath ←
    if ← manifestPath1.pathExists then pure (some manifestPath1)
    else if ← manifestPath2.pathExists then pure (some manifestPath2)
    else pure none

  match manifestPathOpt with
  | none =>
    return "unknown (lake-manifest.json not found near project root)"
  | some actualManifestPath => -- actualManifestPath is guaranteed to exist
    try
      let content ← IO.FS.readFile actualManifestPath
      match Lean.Json.parse content with
      | Except.ok json =>
            let packages := (json.getArr?).toOption.getD #[]
            let mathlibEntry? := packages.find? (fun entry =>
              match entry.getObjValAs? String "name" with
              | Except.ok name => name == "mathlib"
              | Except.error _ => false)
            match mathlibEntry? with
            | some entry =>
                -- Try to get "version" first
                match entry.getObjValAs? String "version" with
                | Except.ok versionStr => if !versionStr.isEmpty then return versionStr else pure ()
                | _ => pure () -- Continue if "version" key is not found or not a string

                -- Fallback to "rev" if "version" was not found or was empty
                match entry.getObjValAs? String "rev" with
                | Except.ok revStr => return revStr
                | _ => pure () -- Continue if "rev" key is not found or not a string

                return "unknown (mathlib entry found, but no version/rev key)"
            | none => pure "unknown (mathlib package not found in manifest)"
        | Except.error err => pure s!"unknown (manifest parse error: {err})"
      catch e =>
        -- Revert back to toString for IO.Error
        pure s!"unknown (error reading manifest {actualManifestPath}: {toString e})"

end ProofTrace
