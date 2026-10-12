# ADR 0010: Compile all Lean code with Lake and reuse outputs from its artifact cache

Date: 2026-10-09. Status: ACCEPTED on 2026-10-12 (PR #76).
Audience: designers and reviewers.
Related: [ADR 0002](adr-0002-compile-project-cache.md),
[ADR 0003](adr-0003-agent-proof-preparation.md),
[ADR 0003 trust extension](adr-0003-trust-extension.md),
[trust boundary](trust-boundary.md),
[latency experiment](../experiments/prepare-latency/README.md),
[Lake cache experiment](../experiments/lake-cache/README.md).

## Context

The verifier's commands compile Lean modules themselves. For each module,
the verifier starts one `lean` process. It also runs `lean --deps-json` two
times for each module: once to discover sources and once more before each
compile. Modules compile one after another, also when they do not import each
other.

Each command starts with an empty temporary workspace. The opt-in stage store
(`MIGRATION_CHECK_STAGE_STORE`) can restore generated stages. ADR 0003 allows
reuse of an approved contract only for closures listed in
`cache_eligibility.py`, after a review of that closure. The list is empty. So
every command compiles the same approved contract again on every run, and CI
compiles the same example contracts again in every test. Most of these CI
compiles come from tests of source `verify` (`cli_test.py`, `atuin_cli_test.py`
and others); fewer tests call `prepare` and `verify-bundle`.

The owner decided on 2026-10-12 to deprecate `verify` in favour of `prepare` and
`verify-bundle`. This ADR covers only those two commands. `verify` keeps its
current path until it is removed, in a separate change; its tests then move to
the two commands and get the benefits of this decision.

A user is likely to keep their Lean files as a Lean project with its own
`lakefile.toml`, and to edit proofs in an editor with the Lean language server.
Today `prepare` takes each file as a separate flag and builds them in a
workspace of its own.

The repository has Lean code of different kinds, and each kind compiles in its
own way today:

| Location | Kind |
| --- | --- |
| `packages/belay-sqlite` | model library, a Lake package |
| `SqliteVerifier/` and the root `.lean` files | verifier library, checker, exporter, conformance runner |
| `VerifierConformance/`, `tools/PublicDoc*.lean` | test-only library, documentation tool |
| `examples/*` | verification cases: contract, candidate and SQL |
| `tests/kernel_gate`, `tests/public_doc_inventory`, `conformance/regressions/*` | fixtures that tests compile directly |
| `experiments/*` | experiment code |

Measured on Linux x86_64 (see the two experiments above). Compile and import
scan time only; export, checker and Python start do not change:

| Work | small | Atuin |
| --- | --- | --- |
| `prepare`, empty workspace, today | 2.35 s | 10.80 s |
| `prepare`, proof edit, today | 0.66 s | 1.13 s |
| `verify-bundle`, today | 1.08 s | 2.96 s |
| Lake, empty cache | 1.08 s | 4.89 s |
| Lake, proof edit, new directory | 0.38 s | 0.38 s |
| Lake, contract only, new directory, warm cache | 0.15 s | 0.18 s |

Lake, the Lean build tool, already does what the verifier needs:

- Each module has a key, its input hash. The key covers the source text, the
  keys and output hashes of the module's imports, the Lean toolchain, options,
  the module name and the package. The workspace path is not in the key.
- Lake keeps outputs in a shared artifact cache (`LAKE_CACHE_DIR`). A new
  workspace with the same sources compiles nothing.
- A changed module whose output does not change does not cause its importers to
  compile again. A comment added to `Requirements.lean` compiled only
  `Requirements`.
- Lake compiles independent modules in parallel and reads import headers itself.

The experiment also showed that the shipped runtime cannot be a Lake package
today. Its `lakefile.toml` requires `lean4export`, which the runtime does not
ship, and the runtime omits `.lake/build/ir`. Each Lake trace lists a `.c` file
there, so Lake decides that every `SqliteVerifier` module is not built.

## Decision

### 1. Lake builds the user's proofs project and the verifier's workspace

**`prepare` builds the user's project.** The candidate's Lean files are a Lake
project: the *proofs project*, with the user's own `lakefile.toml` and
`lean-toolchain`. `prepare`:

- writes the generated modules (`SchemaInputs`, `SqlInputs`, `Generated`) from
  the SQL into a folder of the project that the tool owns, `Generated/`, on
  every run, so they are never stale and nobody runs a generator by hand;
- checks the source rules of section 2. The project reads the approved
  contract in place: its lakefile declares a library whose `srcDir` is the
  approved folder, so there are no copies that could differ (experiment
  finding 11);
- runs `lake build` in the project, with the cache of section 4;
- exports the bundle from the project's outputs.

`prepare` runs in the agent's trust domain (section 4), so it uses the user's
lakefile as it is. Section 10 splits its work into the phases that the proof
author uses: generate, check, audit and export. The user can open the same
project in an editor and run `lake build` without the verifier. A command that
creates the project writes a starting `lakefile.toml` that requires the
verifier's library package (section 3) and a `lean-toolchain` with the pinned
toolchain.

**`verify-bundle` builds its own workspace.** It writes a workspace that
contains copies of the snapshotted approved sources and of the generated
sources it computes itself, a generated `lakefile.toml` and a
`lean-toolchain`, and runs one `lake build`. Its lakefile declares one library
with these modules as roots, enables the artifact cache, sets
`restoreAllArtifacts = true`, and requires the runtime's library package by
path. It never reads the user's lakefile, never runs a `lakefile.lean`, and
never compiles candidate source; this keeps the ADR 0003 rule that acceptance
does not accept candidate `.olean` files.

The generated files in the user's project are a convenience for writing
proofs. They cannot change what is checked: the bundle checker computes the
generated declarations itself and rejects a difference (ADR 0003 P3,
ADR 0008).

### 2. The verifier keeps its source rules

Lake does not know the roles of modules. `prepare` checks the import headers
before Lake runs, so the agent learns about a violation early; `verify-bundle`
checks the approved closure, and its checker rejects exported declarations that
differ from trusted ones. The rules are those of today: approved modules must
not import candidate or reserved modules, and a candidate module must not have
the name of an approved or library module. The verifier reads all headers with
one `lean --deps-json` call for each discovery round, not one call for each
module.

### 3. The runtime ships Lake library packages

The runtime build adds, for `SqliteVerifier` and `belaySqlite`:

- `.lake/build/ir` (about 200 KB for `SqliteVerifier`), so the shipped traces
  are complete;
- a library-only `lakefile.toml` without executables and without
  `lean4export`;
- `enableArtifactCache = false` in both library packages. Library outputs are
  read-only, and Lake must not copy them into the cache.

A user's proofs project requires the library package from the installation in
the same way. The package declares every library that examples and users may
import; today the small example imports `SqliteVerifier.Demonstration` from
`EngineeringExamples` (experiment finding 13). A test builds a generated
workspace and a proofs project against the installed runtime and requires that
Lake compiles no library module.

### 4. One cache for each trust domain

A cache belongs to one **trust domain**: the set of processes that one entity
runs and protects. Any process that can write to a cache can put an output
into it that a later build uses without compiling. Lake's key is a 64-bit hash
that is not cryptographic; it detects accidental change, not attack. So a
cache is only as trusted as every process that can write to it.

- **Same entity runs the commands.** Examples: a developer's
  machine, a CI job, an operator who runs the agent and the verifier under the
  same control. `prepare` and `verify-bundle` can use the same cache freely.
  `verify-bundle` then finds the contract that `prepare` compiled, and the
  reverse.
- **Separate environments.** In production, `verify-bundle` will probably run
  in a separate environment from `prepare`. `verify-bundle` then has its own
  cache, which only the verifier's processes can write. It never reads the
  agent's cache. Only the bundle crosses from the agent to the verifier. The
  verifier's cache still makes repeated checks fast: after the first run for a
  contract, it compiles nothing for that contract.

The cache location is a caller setting: `--cache DIR`, or the environment
variable `BELAY_CACHE_DIR`, with a per-user default under the product's name
(`$XDG_CACHE_HOME/belay/`, or `~/Library/Caches/belay/` on macOS) and one
subfolder for each verifier version. The names follow the product, so they do
not change when the command line tool is renamed. `prepare` and
`verify-bundle` on one machine share the default, because one user is one
trust domain; a separate `verify-bundle` environment has its own.
The caller protects it in the same way as the installation and the approved
sources; the [trust boundary](trust-boundary.md) adds the cache to that list.
A `--no-cache` option compiles everything with an empty, private cache.

### 5. Reuse of approved outputs replaces the eligibility registry

This decision replaces "Approved contract reuse" in ADR 0003 and the
eligibility policy of ADR 0002 §5.2 and §6.1. Reuse of an approved module's
output is allowed from a cache in the same trust domain. The per-closure review
and `cache_eligibility.py` are removed, together with `StageStore` and
`MIGRATION_CHECK_STAGE_STORE`.

Reuse is correct when compiling a module depends only on the inputs in its key.
Evidence: Lake rebuilt `SqliteVerifier.Contract` to a `.olean` that is
byte-identical to the shipped one. The remaining risk is approved Lean code that
reads state outside its key during elaboration: time, randomness, environment or
undeclared files. Lake makes the same assumption for every Lean project. People
review approved code, and such code is easy to see in a review. If the risk is
not acceptable for a contract, the caller uses `--no-cache`.

`prepare` warns, without failing, when an approved module contains commands
that run code during elaboration (`#eval`, `run_cmd`, `initialize`, or `elab`
and `macro` definitions), so the person who reviews the contract sees them.

### 6. Process bounds

Today every `lean` process has its own deadline, output limit and minimal
environment. With Lake:

- `lake build` runs with one deadline for the whole build, a minimal
  environment (`PATH` to the pinned toolchain, `LAKE_CACHE_DIR`, `HOME` in the
  workspace) and bounded captured output;
- Lake's parallel jobs are limited to a configured number;
- the verifier maps Lake's failure output to the same per-module diagnostics as
  today.

### 7. The repository builds its Lean code in three stages

Every Lean file that CI requires to compile is compiled before the tests start,
and its outputs are in the cache that the tests use:

1. **Packages.** Each Lean package (today `belaySqlite` and the verifier
   library with its executables; later also the test-only conformance library
   and the documentation tool) is a Lake package with a `lakefile.toml`. Each
   package is built by its own Nix derivation, which depends on the
   derivations of the packages it requires. The output is the package's Lake
   workspace: sources, lakefile, and `.lake/build` with `.olean`, `.trace` and
   `ir` files. Lake replays such a workspace instead of compiling it (section 3).
2. **Cases.** A verification case has the layout of a user's project, so the
   tests use the input format that users use. A case folder contains the
   project configuration file of the command line tool, `belay.toml`, and a
   proofs project (section 1). `belay.toml` names the schema, the contract
   folder, the migration and the profile. Tests keep the expected status in a
   `[test]` table of the same file, which the tool ignores. Checked-in cases
   are in `examples/<case>/`; cases used only by tests are in
   `tests/cases/<case>/`. A plain `lake build` cannot build a case: its
   generated modules exist only after the verifier writes them, and the keys of
   `verify-bundle`'s workspace contain the package and module names that the
   verifier chooses. So a case is built by running `prepare` and then
   `verify-bundle` on it with one cache, followed by `lake cache stage`.
3. **Tests.** Tests take their cases from `belay.toml` files, not from paths
   in the test code, and use the cache from stage 2.

The folder decides how a Lean file is built. A unit test puts every `.lean`
file of the repository in exactly one category, by its path:

| Category | Path rule | Built in |
| --- | --- | --- |
| Package | under `packages/<name>/` | stage 1 |
| Case | under a case folder (with a `belay.toml`) | stage 2 |
| Direct fixture | listed in the test, for example `tests/kernel_gate/` | by its test |
| Excluded | listed in the test, for example `experiments/` | not built by CI |

A new `.lean` file that is in no category fails the test. So the cache cannot
miss a file without notice. Lean sources that must fail to compile are not
cached, because Lake stores only successful builds; tests write most of them at
run time, and checked-in ones are direct fixtures.

### 8. Tests and CI: one seed for each case

Nix test targets are separate sandboxed derivations that run in parallel. They
cannot share one writable cache directory, and a shared directory would make a
target's result depend on the order of the targets. Instead, Nix builds the
cache once and gives a copy to each target:

- **Seed derivations.** Nix reads the case folders (`builtins.readDir`) and
  makes one seed derivation for each case (stage 2). A seed runs `prepare` and
  `verify-bundle`, so it holds the outputs of both the proofs project and the
  verifier's workspace. Seeds build in parallel, and a change to one case
  rebuilds only its seed. The staged outputs are small: 40 KB for the small
  example, 188 KB for Atuin.
- **Test targets.** Each target that runs `prepare` or `verify-bundle` takes
  the seeds of the cases it uses. Tests of `verify` take none; they move to the
  two commands when `verify` is removed. At start, a target runs `lake cache
  unstage` for each seed into a writable cache in its `$TMPDIR` (inside a
  generated workspace, because Lake stores mappings for each package) and
  passes that cache to the verifier. A test that uses a case as it is compiles
  nothing. A test that changes its inputs compiles only the changed modules,
  and later tests in the same target reuse them.
- **Fixture environment.** Installed-runtime tests give each child a clean
  environment (`runtime_environment` in `conftest.py`). The cache setting is
  added there; a variable set on the derivation does not reach the verifier.
- **Keys do not contain paths.** Targets with different runtime roots
  (`runtime`, `leanRoot`, the conformance runtime) get hits when the library
  contents are the same. A difference causes misses, not wrong results.
- **Reruns.** A seed depends on its case, the runtime and the Python code that
  generates `SchemaInputs`/`SqlInputs`. Targets already run again on runtime
  and Python changes; a case change adds reruns only for the targets that use
  that case. A seed takes about 1 s, or 5 s for Atuin, before its targets start.
- **Trust.** Seeds are built in the Nix sandbox from repository sources, so
  they are in the CI job's trust domain (section 4). Only successful `main`
  jobs save the Nix cache, so a pull request cannot replace a seed that `main`
  uses.

A read-only cache is not used directly: with `enableArtifactCache = true` a
miss fails because Lake writes the new mapping, and with
`enableArtifactCache = false` Lake ignores the cache. The writable copy avoids
both problems.

A named set of tests runs with `--no-cache` and ignores the seeds, so the path
without a cache stays tested. A test checks that a build from the cache and a
build without it give the same verification result. Host runs of
`just test-cases` use a persistent cache under `build/`.

### 9. The toolchain must report its commit

Lake puts the toolchain's commit hash into every key. A Lean built by Nix that
reports a release tag instead of the commit gets keys that never match: in
[ledger/ledger#3270](https://github.com/ledger/ledger/pull/3270), every CI run
compiled all of mathlib for this reason. Our pinned toolchain reports the
commit today. A test checks that `lean --version` reports the commit hash, so
a Lean upgrade cannot silently turn every cache hit into a miss.

### 10. The proof author's loop: generate, check, audit, export

The person or agent who works on a proof needs three things: generate Lean from
the SQL, check the current proof, and export the proof data. The check runs
after every edit and must be fast. Measured on Linux x86_64 with a warm cache
([Lake cache experiment](../experiments/lake-cache/README.md), findings 14–15):

| Phase | What it does | When | Cost |
| --- | --- | --- | --- |
| Generate | Writes `Generated/` from the SQL: `SchemaInputs`, `SqlInputs`, `Generated` with the target statement, and `Check` | When the SQL or the schema changes | about 0.1 s |
| Check | `lake build` of the candidate modules, or the editor's Lean server | After every proof edit | 0.34–0.46 s; per tactic in the editor |
| Audit | `lake build` of the generated `Check` module | On demand: the status command, and before export | 0.7–1.1 s more |
| Export | Writes the bundle for `verify-bundle` | When the proofs are done | 0.4–0.5 s |

`prepare` remains the command that runs all phases. The phases are also
separate commands, so that the loop runs only the check.

**The check is the Lean build.** The target is a generated declaration,
`Generated.expected`, and the proof states `theorem migrationCorrect :
Generated.expected`. Compiling the proof therefore checks it against the exact
generated statement, and Lean's kernel checks each declaration while it
compiles.

**The audit is a generated module.** `Check` imports the proofs and runs an
audit command from the verifier library. The command fails the build, with a
message that names the cause, when:

- the theorem depends on `sorryAx` or on an axiom outside the allowlist of the
  [kernel gate](kernel-gate.md); the command and the gate read one shared
  allowlist, `SqliteVerifier.allowedAxioms`;
- the proofs import a module that is not in the verifier library, the approved
  contract, the generated modules or the proofs project, because
  `verify-bundle` would not have it.

The audit command needs Lean's elaborator, so `Check` imports `Lean`, which
takes about 0.5 s to load. That is why the audit is not part of the per-edit
check.

**Options that turn off checks.** The audit cannot see an option such as
`debug.skipKernelTC` that a proof module sets for itself: an option applies to
the module that sets it, and the `.olean` does not record it. Generation
rejects such options in the TOML lakefile (`leanOptions`, `moreLeanArgs`). An
option set in a Lean source file can make the local check green; it cannot
make a result verified, because `verify-bundle` replays every declaration in
the kernel.

**Why the check is fast:**

- No process other than Lake and Lean runs: no Python, no export, no second
  kernel run. The independent replay is the verifier's job.
- Lake's artifact cache supplies the library, the contract and every unchanged
  module (section 4); a proof edit compiles one module. An edit that leaves a
  module's `.olean` unchanged, such as a comment, rebuilds nothing after it.
- Generation writes a file only when its content changes, so it never causes a
  rebuild by itself. A SQL change recompiles only the modules that import
  `SqlInputs`.
- The proofs project is an ordinary Lake project, so agents can use the Lean
  language server through tools such as
  [lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp): goals, diagnostics
  and lemma search without a build. `lake build` confirms.
- A new session starts with a warm cache: the user's cache, a cache filled from
  CI's seeds, or Lake's remote cache service. This is safe on the agent's side;
  `verify-bundle` keeps its own cache (section 4).

The time of the proof itself stays. In Atuin, `AtuinWitness` takes 2.4 s
because it uses `decide` on large terms; the remedy is library lemmas that make
common proofs cheap, not the build.

**What the local check and audit do not do,** and how the difference is kept
small:

| `verify-bundle` also | Locally |
| --- | --- |
| Generates the target from the SQL itself | The same generator writes `Generated/`; a difference means a stale folder, and the next generation removes it |
| Replays every declaration in an independent kernel | Lean's own kernel checks each declaration during compilation, unless a source file turns that off (see above) |
| Accepts declarations only from the installed library and the approved contract | The audit reports other imports |
| Uses the approved contract | The proofs project reads the contract in place from the approved folder (section 1), so there is no copy that can differ |

The local check decides nothing. A verified result comes only from
`verify-bundle`, in the verifier's trust domain
([ADR 0011](adr-0011-product-trust-and-development-integrity.md), section 1).
The audit command is a convenience for the proof author, not part of the
product trust base; the kernel gates stay the only judges.

### 11. CI times are tracked during the implementation

The tasks of this ADR change how CI compiles. Each change must show its effect
on CI time, so that a regression is found when it is introduced:

- Before the first task starts, the times of the latest successful `main` runs
  are recorded as the baseline: each CI job on Linux and macOS, for each scope
  that ran, with the cache state.
- Each pull request of these tasks records the times of its CI jobs in the
  task's status file, next to the latest `main` run with the same scope and
  cache state.
- A big increase is investigated before the merge, and the pull request
  explains it: what became slower, why, and whether it is fixed or accepted.
  The starting threshold is a job that is 20 % or 2 minutes slower, whichever
  is larger; runner noise of hosted CI is about that size.
- After each task, `docs/ci-performance.md` gets one line with the job times.

## Consequences

- `prepare` and `verify-bundle` stop compiling unchanged modules. CI compiles
  each checked-in case once, in its seed.
- The user keeps proofs in an ordinary Lake project: `lake build` and the
  editor's Lean server work on it without the verifier.
- The proof author's loop is a Lean build of one module, 0.34–0.46 s after a
  proof edit instead of 1.4–2.0 s for `prepare` today; the audit adds
  0.7–1.1 s when it runs. Most iterations need no build when the agent uses
  the language server. Expected
  acceptance time for Atuin: about 3.5 s instead of 6.6 s, most of it the
  bundle checker. Expected `prepare` time after a proof edit: under 1 s instead
  of about 2 s.
- The verifier no longer runs `lean --deps-json` before each compile.
- Tests name cases through their folders. Adding a case means adding a folder
  with a `belay.toml` and a proofs project; adding any other Lean file means
  placing it in a category of section 7.
- Lake becomes part of the trusted implementation. Its cache format and
  behavior can change with each Lean release, and the project follows each
  stable release (see "Lean maintenance" in [CLAUDE.md](../CLAUDE.md)). An
  upgrade must run the cache tests.
- Caches grow mostly across upgrades: each Lean release makes the entries of
  the previous one useless. The default cache keeps one subfolder for each
  verifier version, and a clean command deletes all subfolders except the
  current one. There is no size limit; a contract adds about 0.25–3 MB.
- The trust milestone ([ADR 0003 trust extension](adr-0003-trust-extension.md))
  is compatible: hostile agents run `prepare` in their own trust domain, and
  `verify-bundle` keeps a cache that agents cannot write.

## Evidence

The [Lake cache experiment](../experiments/lake-cache/README.md) checked each
part of this decision on Linux x86_64:

- reuse across workspaces, cutoff on unchanged outputs, read-only caches, and
  `stage`/`unstage` (findings 1–10);
- an installation whose libraries are Lake packages, a user's proofs project
  with its own lakefile that requires it and reads the contract in place, and
  the installed exporter and bundle checker on Lake's outputs: VERIFIED for
  the small and Atuin examples, VIOLATED for the refutation (findings 11–13);
- the per-edit check and the audit command, with its failure cases
  (findings 14–15);
- the seed in the Nix sandbox: fresh workspaces built from an unstaged seed
  compile nothing (finding 16).

These are left to the implementation tasks, because they carry no design risk:
mapping Lake failures to per-module diagnostics; macOS, which the tasks' tests
cover on the macOS CI runner; and the cleanup of caches (see "Decisions").

## Decisions

The owner decided on 2026-10-12:

1. **Reuse within a trust domain (section 5)** replaces ADR 0003's per-closure
   review. The owner accepts the remaining risk: approved Lean code that reads
   the clock, the environment or undeclared files during elaboration can make
   a cached output differ from a fresh one. Such code makes the meaning of the
   contract unstable also without a cache; `prepare` warns about it, and
   `--no-cache` avoids the cache.
2. **Cache options (section 4)** are implemented now: `--cache DIR`,
   `--no-cache`, `BELAY_CACHE_DIR`, and a per-user default named after the
   product.
3. **Cache cleanup (Consequences):** no size limit; one subfolder for each
   verifier version in the default cache, and a clean command that removes
   the subfolders of other versions. The documentation also names
   `lake cache clean`.
4. **CI times are tracked during the implementation (section 11).**

## Plan

Each step is a separate task with its own tests; the order follows the
dependencies:

Each task records CI times as section 11 describes.

1. [Case folders and the Lean file categories](../plans/20261012-case-manifests-and-lean-categories.task.md):
   each case gets a `belay.toml`, tests read them, and the coverage test of
   section 7. The candidate files move into a proofs folder only in step 2,
   when `prepare` can build it.
2. [Lake builds in the verifier](../plans/20261012-lake-builds-in-the-verifier.task.md):
   runtime library packages (section 3), `prepare` on a proofs project with
   the generate, check, audit and export phases (sections 1, 10), `verify-bundle` on
   its own workspace (sections 1, 2, 6), the cache options
   (section 4), and removal of the stage store (section 5). The cases become
   proofs projects.
3. [Case seeds in CI](../plans/20261012-case-seeds-in-ci.task.md): seed
   derivations and their use in the test targets (section 8), and the
   toolchain commit check (section 9).
4. [Verifier library as a package](../plans/20261012-verifier-library-package.task.md):
   the verifier library, the test-only conformance library and the
   documentation tool move under `packages/` (stage 1 of section 7).

The removal of `verify` is a separate change and not part of this plan.

## Alternatives considered

- **Keep the stage store and fix the orchestration** (the latency experiment's
  prototypes). Faster, but each command still compiles the contract unless the
  registry lists it. The registry needs a review of each user contract, which
  does not scale.
- **A per-module key in the stage store.** This copies Lake's design, without
  the cutoff on unchanged outputs, the parallel builds and Lake's maintenance.
- **A cache made by Nix for CI only.** It helps CI, not users.
- **A Lake and Nix integration** ([lean4-nix and lake2nix](https://github.com/lenianiva/lean4-nix),
  or `buildLakePackage` in nixpkgs). Both build one derivation for each
  package and let Lake reuse modules inside it; neither shares modules between
  our test targets, and both add a dependency that must follow every Lean
  release. Lean's own Nix support built one derivation for each module; it was
  removed before Lean 4.11. Users run `verify-bundle` without Nix, so Lake's
  cache is the mechanism in any case.
- **Lake's remote cache services** (Lean 4.30). They would share outputs
  across CI runs, but without signing and with a 64-bit key they are safe only
  inside one trust domain. The Nix cache, saved only from `main`, already
  does this.
- **`verify-bundle` runs Lake on the user's own project.** Rejected: a user's
  lakefile can run code (`lakefile.lean`, or packages that `require` fetches)
  and can load native code or change compiler options, and `verify-bundle`
  runs in the verifier's trust domain. It also needs its own snapshot and role
  rules. `prepare` uses the user's project (section 1) because it runs in the
  agent's trust domain, where the user's own code is already trusted, and the
  bundle checker does not depend on how the bundle was built.
