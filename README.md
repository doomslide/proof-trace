# proof-trace: Extracting Self-Contained Theorems and Proofs from Lean 4

This is a tool to extract intermediate goals from typed lean proofs and represent them as self-contained theorems with their corresponding proofs. It also includes a utility for sampling theorems from Lean libraries (e.g. Mathlib).

## Prerequisites

*   **Lean 4 & Lake:** Ensure you have a working Lean 4 environment with `lake` (the Lean build tool). You can install it using `elan`. See [Lean installation instructions](https://leanprover-community.github.io/install/linux.html).
*   The project is configured to use a specific Lean toolchain version (see `lean-toolchain` file).

## Setup

1.  **Clone the repository:**
    ```bash
    git clone https://github.com/doomslide/proof-trace
    cd proof-trace
    ```

2.  **Update Lean Dependencies:** Fetch the required Lean libraries (e.g., mathlib, batteries). This step is crucial for accessing libraries like Mathlib and will download their precompiled versions (cache) if available.
    ```bash
    lake update
    ```

3.  **Build Lean Executables:** Compile the tools. The `proofTrace` executable is a default target.
    ```bash
    lake build
    # This will build all default targets, including proofTrace.
    # To build specific executables:
    # lake build proofTrace
    # lake build sampleProofs
    ```

## Overview of Tools

This project provides two main executables:
*   `proofTrace`: For processing individual Lean files to extract theorem data and proof steps.
*   `sampleProofs`: For sampling theorems from a broadly loaded environment based on module prefixes.

## `proofTrace` Executable

This executable, built from `ProofTrace/Main.lean`, provides commands to process Lean files.

**Usage:**
To run `proofTrace` use `lake exe`:
```bash
lake exe proofTrace -- [COMMAND_NAME] [ARGS...]
```
Alternatively, after building with `lake build proofTrace`, you can run it directly:
```bash
./build/bin/proofTrace [COMMAND_NAME] [ARGS...]
```

**Commands:**

### `fromFile` Command
Processes a single Lean source file, extracting theorem data.

*   **Usage Example:**
    ```bash
    lake exe proofTrace -- fromFile --src <inputFile.lean> --out <outputFile.jsonl> [--norm <mode>]
    ```
*   **Arguments for `fromFile`:**
    *   `--src <inputFile.lean>`: (Required) Path to the input Lean source file.
    *   `--out <outputFile.jsonl>`: (Required) Path where the output JSONL data will be saved.
    *   `[--norm <mode>]`: (Optional) Normalization mode for proof states. Modes: `all`, `default`, `reducible`, `instances`. Defaults to `reducible`.

*   **Normalization Modes (`--norm`):**
    Normalization in Lean refers to the process of unfolding definitions to a certain degree. Different modes control how "aggressively" definitions are expanded. This can affect the specific form of the extracted `goal` and `proof` terms in the output.
    *   `all`: Unfolds all constants, even those marked as `@[irreducible]`.
    *   `default`: Unfolds constants except those marked `@[irreducible]`.
    *   `reducible`: Unfolds only constants explicitly marked `@[reducible]`. This is often used to see a more abstract or high-level view of a proof state.
    *   `instances`: Unfolds reducible constants and constants marked `@[instance]`.

## Detailed Example: Using `proofTrace`

This example demonstrates how to use `proofTrace` to process a Lean file and extract proof trace data.

**1. Example Input File (`examples/lean/test1.lean`):**

First, ensure you have an example Lean file. For instance, the project includes `examples/lean/test1.lean` with the following content:

```lean
import Mathlib.Data.Nat.Basic

theorem add_assoc_example (a b c : Nat) : a + b + c = a + (b + c) := by
  rw [Nat.add_assoc]
```

**2. Command to Process the File:**

Run the following command from the root of your project (`proof-trace/`):
```bash
lake exe proofTrace -- fromFile --src examples/lean/test1.lean --out examples/jsonl/test1_out.jsonl --norm reducible
```

This command will:
*   Invoke the `proofTrace` executable.
*   Use the `fromFile` subcommand.
*   Process the source file `examples/lean/test1.lean`.
*   Write the output to `examples/jsonl/test1_out.jsonl`.
*   Use `reducible` normalization mode.

**3. Example Output (`examples/jsonl/test1_out.jsonl`):**

After running the command, the `examples/jsonl/test1_out.jsonl` file will be generated. It contains a JSON object on each line, representing an extracted proof step or state.
(An example of such an output file is also present in the repository at `examples/jsonl/test1_out.jsonl` for reference).

**Understanding the Output Fields:**

Let's break down the fields of a typical JSON object from the output. Each line in the `.jsonl` file is a similar JSON object (`_comment` fields are purely pedagogical and do not appear in the actual file ^^).

```json
{
  "_comment": "A unique identifier for this proof state/goal."
  "syntheticName": "add_assoc_example_goal_goal_12739406252616973674",

  "_comment": "Original theorem/declaration name in the source file."
  "sourceDecl": "add_assoc_example",

  "_comment": "Active local context (hypotheses, variables) for this proof state."
  "context": [
    "(a : ℕ)",
    "(b : ℕ)",
    "(c : ℕ)"
  ],

  "_comment": "Goal statement to be proven at this proof stage."
  "goal": "a + (b + c) = a + (b + c)",

  "_comment": "Lean proof term for the `goal` in its `context`."
  "proof": "Eq.refl (a + (b + c))",

  "_comment": "Prettified version of the `proof` term (often identical)."
  "prettyProof": "Eq.refl (a + (b + c))",

  "_comment": "Definitions, theorems, and axioms that `proof` and `goal` depend on."
  "primitives": {
    "primitives": [
      {
        "value": "fun α => α",
        "type": "Sort u → Sort u",
        "name": "outParam",
        "kind": "definition"
      },
      {
        "value": "fun {α} [Add α] => { hAdd := fun a b => Add.add a b }",
        "type": "{α : Type u_1} → [Add α] → HAdd α α α",
        "name": "instHAdd",
        "kind": "definition"
      }
      "_comment": (list continues with other primitive objects)
    ]
  },

  "_comment": "For potential distractor/related-but-incorrect proof terms. (Not implemented here.)"
  "distractors": [],

  "_comment": "Lean version used during processing."
  "leanVersion": "4.20.0-rc5",

  "_comment": "Detected Mathlib version (if found)."
  "mathlibVersion": "unknown (mathlib package not found)",

  "_comment": "Placeholder for exact original source module path (not yet implemented)."
  "originalSource": "[source extraction not implemented]"
}
```

## `sampleProofs` Executable

This executable, built from `scripts/SampleFromPrefix.lean`, samples theorems from a broadly loaded environment based on a module prefix. For example, it can load the entire `Mathlib` library and then sample theorems specifically from modules starting with `Mathlib.Data.List`. Use with caution: may result in enormous jsonl from the dependency closure alone.

**Usage:**
```bash
lake exe sampleProofs -- <num_samples> <sublibrary_prefix> <output_file.jsonl>
```

**Arguments:**

*   `<num_samples>`: (Required) The number of theorems to attempt to sample.
*   `<sublibrary_prefix>`: (Required) The prefix for module names from which to sample theorems (e.g., `Mathlib.Data.List`, `ProofTrace.Data`). The script first ensures a relevant base library (like `Mathlib` if the prefix is `Mathlib.*`) is loaded, then filters theorems from modules in the resulting environment that start with this prefix string.
*   `<output_file.jsonl>`: (Required) Path to the output JSONL file where sampled theorem data will be written.

**Example Usage:**

To sample 10 theorems from Mathlib (WARNING: output will be HUGE) modules starting with `Mathlib.Data.Nat` and save them to `output/sampled_nat_theorems.jsonl`:
```bash
lake exe sampleProofs -- 10 Mathlib.Data.Nat output/sampled_nat_theorems.jsonl
```
This command will load the necessary parts of `Mathlib`, find theorems in modules like `Mathlib.Data.Nat.Basic`, `Mathlib.Data.Nat.Prime`, etc., and write the data for up to 100 of them into the specified output file. The output format for each theorem will be similar to the JSON objects described in the `proofTrace` example.