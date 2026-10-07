# Reproducing the verification

The repository fixes Lean `4.29.0`, the mathlib commit, and the transitive dependency revisions in `lake-manifest.json`. Python 3.10 or later is used for source-integrity and verification scripts.

## Build the library

Install [elan](https://github.com/leanprover/elan) and make its tools available on `PATH`. From the repository root, run:

```sh
lake update
lake exe cache get
lake build
```

`lake build` builds both default targets: `CriticalGK2`, which imports the complete theorem dependency graph, and `Verification`, which prints the five main theorem signatures and their axiom dependencies.

## Check source integrity

```sh
python3 scripts/check_manifest.py
```

`verification/source-manifest.json` records SHA-256 hashes for every Lean source file. The script checks the file set and each hash. It uses the Python standard library.

## Run a fresh compiler check

```sh
lake env python3 scripts/verify.py
```

The script checks the pinned environment, orders project files by their imports, and invokes Lean on each source file. Every project file is compiled during the run. It then extracts axiom dependencies from compiler output and checks the five principal declarations. Results are written to `verification/local-report.json`.

The report includes relative source paths, source hashes, compiler exit codes, and axiom queries. The allowed foundational dependencies are `propext`, `Classical.choice`, and `Quot.sound`. The script also scans project sources for incomplete proofs and additional axiom declarations.

## Release record

The release verification is recorded in [kernel-check.json](../verification/kernel-check.json). Its hashes identify the source version checked by Lean. The five endpoint queries correspond to the declarations in [Verification.lean](../Verification.lean).

The release run compiled all 145 project files afresh and completed 230 axiom-dependency queries covering 225 distinct declarations. All five required endpoints were checked. The dependency sets contain only `propext`, `Classical.choice`, and `Quot.sound`.

The standard `lake build` command also completed successfully for both default targets.

The mathematical statements and conventions are documented in [Formalization](FORMALIZATION.md), and the historical sources are listed in [Background and references](HISTORY.md).
