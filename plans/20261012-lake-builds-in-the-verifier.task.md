# Lake builds in the verifier

Created 2026-10-12. Status: READY.
Decision: [ADR 0010](../docs/adr-0010-lake-builds-and-artifact-cache.md),
sections 1–6 and 10. Accepted on 2026-10-12.
Evidence: [Lake cache experiment](../experiments/lake-cache/README.md),
[latency experiment](../experiments/prepare-latency/README.md).

## Outcome

1. The installed runtime contains Lake library packages for `SqliteVerifier`
   and `belaySqlite`: sources, a library-only `lakefile.toml` (no executables,
   no `lean4export`), `enableArtifactCache = false`, and complete `.lake/build`
   outputs including `ir`. A generated workspace that requires them compiles no
   library module.
2. `prepare` builds the user's proofs project (ADR 0010 section 1): a Lake
   project with the user's own `lakefile.toml` and `lean-toolchain`. On every
   run it writes the generated modules into the project's `Generated/`
   folder, runs `lake build` in the project and exports the bundle. The
   project reads the approved contract in place: its lakefile declares a
   library whose `srcDir` is the approved folder.
   A command creates a proofs project with a starting `lakefile.toml` that
   requires the installed library package, and a `lean-toolchain`.
3. `verify-bundle` compiles only approved and generated modules, in a
   workspace it generates itself (snapshotted sources, generated
   `lakefile.toml` and `lean-toolchain`, one `lake build`). It never reads the
   user's lakefile.
4. The phases of ADR 0010 section 10 are separate commands, and `prepare`
   runs all of them:
   - generate writes `Generated/` (including the `Check` module) and changes a
     file only when its content changes;
   - check is `lake build` of the candidate modules, after every edit;
   - audit is `lake build` of the generated `Check` module, on demand (status
     and before export). Its command from the verifier library fails the build
     on `sorry`, an axiom outside the gate's allowlist, or an import that
     `verify-bundle` would not have. The allowlist is shared with the gate,
     not copied. Generation rejects options that turn off checks in the TOML
     lakefile (`leanOptions`, `moreLeanArgs`);
   - export writes the bundle from the built project.
   The audit command is not part of the product trust base; `verify-bundle`
   stays the only verdict.
5. The checked-in cases become proofs projects, and their tests and the
   experiment scripts use them.
6. The source rules of today stay: approved modules cannot import candidate or
   reserved modules, and a candidate module cannot take the name of an
   approved or library module. `prepare` reports a violation before Lake runs;
   `verify-bundle` enforces the rules. Headers are read with one
   `lean --deps-json` call for each discovery round.
7. `prepare` and `verify-bundle` accept `--cache DIR` and `--no-cache`, and
   read `BELAY_CACHE_DIR`. Without either, they use the per-user default
   (`$XDG_CACHE_HOME/belay/`, `~/Library/Caches/belay/` on macOS) with one
   subfolder for each verifier version. A clean command removes the
   subfolders of other versions. `--no-cache` compiles everything in a
   private, empty cache.
8. `prepare` warns, without failing, when an approved module contains commands
   that run code during elaboration (`#eval`, `run_cmd`, `initialize`, `elab`
   or `macro` definitions).
9. `lake build` runs with one deadline, a minimal environment, bounded captured
   output and a bounded number of parallel jobs. A compile failure gives the
   same status and the same kind of per-module diagnostic as today.
10. `StageStore`, `MIGRATION_CHECK_STAGE_STORE`, the measurement override,
   `cache_eligibility.py` and their tests and documentation are removed.
   ADR 0003 and the trust boundary document describe the new cache rule.
11. Statuses and exit codes of `prepare` and `verify-bundle` are unchanged for
   every existing test case. `verify` keeps its current compile path; it is
   deprecated and removed in a separate change.

## Tests

- Runtime: a generated workspace against the installed runtime builds with
  zero library compiles; Lake runs with the runtime's library outputs read-only.
- User project: `prepare` on a proofs project whose lakefile the user
  changed (an extra module root, an extra option) builds and exports; `lake
  build` in the project works without the verifier; a stale or edited
  `Generated/` folder does not change the result of `verify-bundle`; a changed
  copy of an approved module is reported by `prepare` and rejected by
  `verify-bundle`.
- Audit: building `Check` fails, naming the cause, for a proof that uses
  `sorry`, one that uses an axiom outside the allowlist, and a proof module
  that imports a module the installation does not have; generation refuses a
  lakefile that sets `debug.skipKernelTC`. A correct proof builds green, and
  `verify-bundle` accepts its export.
- Loop speed (recorded in the status file, not a test): add a theorem to
  `Proofs.lean` and build the candidate, on the small and Atuin examples; the
  experiment measured 0.34–0.46 s for the check and 0.7–1.1 s more for the
  audit.
- Generation is stable: running generate twice changes no file and causes no
  rebuild.
- Reuse: a second run of each command on the same inputs, in a new temporary
  directory with the same cache, compiles no module; after a proof edit,
  `prepare` compiles only the changed candidate modules.
- Cache options: `--cache DIR`, `BELAY_CACHE_DIR` and the default each select
  the expected folder, with a subfolder for the verifier version; the clean
  command removes other versions' subfolders and keeps the current one.
- Elaboration warning: `prepare` on a contract with `#eval` in an approved
  module warns and still prepares; without such commands it does not warn.
- Trust domains: `verify-bundle` with its own empty cache verifies a bundle
  that `prepare` made with a different cache.
- Equivalence: for each checked-in case, the result with a warm cache equals
  the result with `--no-cache`.
- Source rules: the existing attack and import-rule tests pass, with the
  rejection before Lake runs.
- Failures: a candidate compile error gives `UNVERIFIED` and names the module;
  a `lake build` over its deadline is stopped and reported.
- End to end through the installed runtime: `bundle_test.py`,
  `proof_exporter_test.py`, `runtime_package_test.py`; the tests of `verify`
  (`cli_test.py`, `atuin_cli_test.py`, `kernel_gate_test.py`) keep passing
  unchanged.
- Timing (recorded in the status file, not a test): the experiment scenarios
  of `experiments/lake-cache/` through the real commands, on Linux and macOS.

## Relevant source and constraints

- Compilation today: `migration_check/compile.py` (`compile_modules`,
  `compile_project`), `migration_check/contract.py` (`compile_trusted`,
  `run_stage`), `migration_check/prepare.py`, `migration_check/bundle.py`,
  `migration_check/source_closure.py` (`discover_sources`, `imports`,
  `lean_process`), `migration_check/import_path.py`
  (`merged_search_path`), `migration_check/runtime.py` (`Runtime.locate`,
  `validate_libraries`).
- The runtime is assembled in `build-support/runtime.nix` from `leanRuntime`
  (`build-support/default.nix`, which copies only `.lake/build/lib/lean`) and
  `modelPackage`. The root `lakefile.toml` requires `lean4export` at
  `build/lean4export`.
- Lake ignores `LEAN_PATH` when it compiles; libraries must be packages.
- Lake wants `enableArtifactCache` set in the generated workspace and absent or
  `false` in the read-only libraries; see the experiment's findings 4 and 8.
  Without a `lean-toolchain` file, Lake writes one and stops.
- `restoreAllArtifacts = true` is needed: the exporter, the bundle checker and
  the gate read `.olean` files from the workspace, not from the cache.
- The target statement already exists as `Generated.expected`
  (`migration_check/compile.py`, `EXPECTED_SOURCE`); proofs state
  `theorem migrationCorrect : Generated.expected`.
- The gate's axiom allowlist is written inline in `GateCore.lean`
  (`[propext, Classical.choice, Quot.sound]`). It must become one named
  declaration that the gate and the audit command both use, so they cannot
  drift apart. The gate files are in the product trust base (ADR 0011
  section 6); the audit command is not.
- The audit command imports `Lean`, about 0.5 s to load; that is why it is not
  in the per-edit check. It cannot see an option that a proof module sets for
  itself (experiment finding 15).
- A comment-only edit leaves the `.olean` byte-identical, and Lake then
  rebuilds nothing that imports it; timing tests must change a declaration.
- The installation's library package must declare `EngineeringExamples`, or
  the examples must stop importing `SqliteVerifier.Demonstration`
  (experiment finding 13).
- `experiments/lake-cache/installation.nix`, `data_path.py` and
  `check_loop.py` are working prototypes of the runtime packages, the data
  path and the audit command.
- A user's lakefile may contain anything, including `require` of other
  packages; `prepare` runs in the agent's trust domain and uses it as it is.
  What `verify-bundle` cannot accept (for example declarations from a package
  the installation does not have) should be reported by `prepare`.
- Lake's cache key is a 64-bit, non-cryptographic hash. Caches are safe only
  within one trust domain (ADR 0010 section 4); the documentation must say
  that the caller protects the cache directory.
- Today each `lean` process is bounded by `migration_check/process.py`
  (`run_process`); Lake starts `lean` itself.
- `Popen.wait(timeout=...)` polls with sleeps of up to 50 ms; the latency
  experiment measured this cost per child process.
- The trust milestone forbids accepting candidate `.olean` files on the data
  path; `verify-bundle` must never build candidate modules.
- CI times: record the baseline and each pull request's job times in the
  status file, and investigate a big increase before the merge (ADR 0010
  section 11).
