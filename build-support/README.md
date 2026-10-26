# Immutable project builds

Run `nix-build build-support/default.nix -A conformance --no-out-link` with Nix's
`flakes` experimental feature enabled (`builtins.fetchTree` needs it). This is an
ordinary Nix expression. The flake in `nix/flake.nix` also exposes the same test
derivations as `checks.<system>`. The development shell remains
`nix develop path:./nix`, with the existing `nix/flake.lock` pin.

Targets `leanToolchain`, `parserLibrary` and `conformance` share the locked
nixpkgs input. Derivations build offline after their declared archives/packages
are fetched. Lean is exactly 4.34.1; neither Elan nor a nixpkgs Lean version is
used. Linux binaries use the pinned loader via autoPatchelf. Darwin upstream
binaries already use bundled-relative/platform loaders.

`docGen4` builds the exact doc-gen4 v4.34.1 manifest closure.
`apiReferenceCore` builds the doc-gen4 database for Lean's `Init` and `Std`
from the toolchain and doc-gen4 only. `apiReferenceBase` adds the public Lean
library to a copy of it and writes the HTML reference, with a placeholder in
its source links, so it does not change with the commit.
`apiReference` copies it and puts the required `referenceRevision` full commit
hash into the source links. `just reference HASH`
runs it in a sandbox and links the output at `build/api-reference`. These
targets are separate from `conformance` and its closure. See the
[API reference guide](../docs/api-reference.md).

`theoremDependencies` reads the compiled model, codec, text, surface and
conformance libraries. `just theorem-dependencies` writes an offline HTML
browser and JSON graph at `build/theorem-dependencies`. The
[dependency guide](../docs/theorem-dependencies.md) explains coverage, helper
paths and optional existing proof costs. `tests.theoremDependencies` checks
the exporter and report against compiled fixtures.

Reference generation corrects links to recursors that doc-gen4 omits to the
existing parent-type anchors. It also corrects the Lean 4.34.1 TacticsExtra
docstring's `Init/Tactic.html` link to `Init/Tactics.html`. The remaining
missing pages and anchors fail validation. The standard `#top` fragment,
named anchors and raw/decoded HTML IDs remain valid targets.

`parserLibrary` builds the in-process SQLite parser library, as
[ADR 0007](../docs/adr-0007-parser-library.md) decides. Nix owns all parser
build reuse; there is no separate local builder or content-stamp cache. The
release derivations verify upstream checksums; `parser/generate.py` verifies
token agreement and transforms the grammar before Nix compiles and links the C
sources. Nix reads
`parser/dialects.json` and makes one derivation for each release
(`parserLibrary.releases`), one for each distinct grammar identity
(`parserLibrary.grammars`) and one that links `parserLibrary.library`, so a new
release or grammar builds only its own derivations. `parser/library_steps.py`
does the checks between the Lemon and compiler steps. The test suite
`tests.parserLibrary` checks the library. The translation program of `conformance`
links it by its path in the Nix store. See the [SQLite syntax boundary](../docs/sqlite-parser.md).

`parserLibrary.grammars` retains each grammar's Lemon outputs and generated
parser. Each Lean package under `packages/` has its own `lakefile.toml` and its
own derivation (`lean-package.nix`), which builds it once, in a copy of the
repository layout that holds the outputs of the packages it requires. Lake
replays those outputs and compiles only the package's own modules; the output
is the package's Lake workspace. `tests.packages` checks that a workspace that
requires an output compiles nothing. The packages are `modelPackage`
(`packages/belay-sqlite-model`: `Belay.Sqlite.Model` and its codec),
`verifierConformance` (`packages/verifier-conformance`: the test-only conformance
library and runner), `docTools` (`packages/public-doc-tools`: the documentation
inventory), `textPackage` (`packages/belay-sqlite-text`: the parser library's binding and
the translation of SQL text, linked with the parser library) and `surfacePackage`
(`packages/belay`: the surface, which requires the text package).
The harness sends SQL text to the text package's translation program
(`belay-sqlite-translate`) in `conformance`, which gives the model's statement syntax. The
conformance runner resolves statement syntax itself.
`just build` builds `conformance` at `build/conformance`; it does not rebuild Lean through
Elan or Lake outside Nix, and it writes nothing into the checkout's `packages/`. The test
recipes use `build/conformance` as their runtime root; set `SQLITE_VERIFIER_RUNTIME_ROOT` to
use another immutable runtime output. Reports remain in the checkout's `build/`, so the
runtime itself needs no mutable staging copy.

`just test-nix` runs `tests/test_source_identity.py`, which
checks each declared input through real Nix source identities. Each declared input relation and component-level
ignore rule is selectable; cases cover additions, edits, renames, deletions and
missing required inputs. CI runs
them for the `infrastructure` and `full` scopes. Fixtures contain tiny
synthetic inputs; they never copy a checkout or build a package.

Lean archive digests come from the official GitHub v4.34.1 release asset metadata.
Nix verifies each downloaded archive against its pinned digest. Native build
and loader checks must pass on both supported platforms;
evaluating Linux derivations on Darwin does not validate Linux execution.
The [upgrade status](../plans/20261006-lean-4-34-1-upgrade.status.md) records
the actual verification evidence.

`tests.model`, `tests.frozen`, `tests.harness`, `tests.sample`, `tests.upstream`,
`tests.corpora`, `tests.parserLibrary`, `tests.packages`, `tests.documentation`,
`tests.surface` and `tests.surfaceChecks` are independent pytest derivations declared in `tests.nix`. `tests/nix_suites.json` gives their test-file ownership and also
drives the host `--source-checks` exclusions. The model, coverage, frozen and
harness inputs are shared pytest support, pinned Python/pytest, their explicit
conformance helpers, the SQL frontend modules in `tests/conformance_frontend.json`,
parsers and pinned SQLite; only frozen adds the frozen corpora and retained reports.
Conformance targets exclude unrelated tests and documentation. Changes to shared
pytest support invalidate every suite. Nix owns all result reuse.
The sample owns the frozen v4 and synthetic inputs plus their shared replay and
validation helpers. Full-only historical evidence and tests do not invalidate it.
`developmentTests` selects every target except `tests.model`, the coverage suites
(`tests.coverageStatements`, `tests.coverageFeatures`), `tests.frozen` and `tests.corpora`;
the full target set remains in CI.

`publicDocumentation` checks the compiled public import closure against its
source parser and original compiler references. Every authored public
declaration, constructor and field must have direct checked Verso documentation.
Missing, ordinary and unclassified documentation fail this development target.
`just test`, `just test-full` and reference generation run this gate. Its
inventory tool is the `docTools` package (`packages/public-doc-tools`) with the
Python driver `tools/public_doc_inventory.py`; neither is in the conformance
runtime. `tests.documentation` runs the inventory on small fixtures.

`conformanceRuntime` holds only the outputs of `verifierConformance`: the
`VerifierConformance` Lean library and the test-only `conformance-runner`.
`conformance` assembles its compiler, library and parser links. `tests.model` uses
this runtime, including native acquisition and the model-mutation checks.
Changes inside `packages/verifier-conformance/` invalidate only the conformance
package, not the model.
Use `just conformance-build`, then `python3 -m pytest tests/conformance_model_test.py
--runtime-root build/conformance`, to force a focused local run. `just conformance
--repeat 3 --prove` writes the prototype's JSON cases, proofs and timing report.
The native engine uses its default build configuration. The runner checks version,
source ID and MAX_COLUMN, then verifies library-default DQS_DML/DQS_DDL on every
connection. The shell fixture runner enables both to match the library profile.

Flake equivalence tests stage a temporary Git source boundary so the real Nix 2.18
subdirectory-flake command also works from a dedicated Jujutsu workspace without
a colocated `.git`. The project itself continues to use Jujutsu.

Run all checks of `tests` through the flake:

```sh
nix flake check ./nix -L \
  --option sandbox true --option sandbox-fallback false \
  --extra-experimental-features 'nix-command flakes'
```

Use `./nix` for checks: Nix includes the Git repository, allowing the subdirectory
flake to access project sources above it. `path:./nix` copies only that directory
and is suitable for the standalone development shell, not project checks.
`--no-build --all-systems` evaluates both platforms without running their tests.

The installed Nix 2.18 cannot create result links from `flake check`, so `just test`
builds `developmentTestReports`, which links each suite of `developmentTests` under its
name in `build/nix-tests` (for example `build/nix-tests/harness/junit.xml`).
`just test-full` builds `testReports`, with all `tests` in `build/nix-tests-full`, and
`just test-scheduled` builds `scheduledTestReports` in `build/nix-tests-scheduled`;
CI keeps these folders.
`just test-cases tests/conformance_model_test.py` forces an ordinary
pytest run. The non-flake `nix-build -A tests.model` entrypoints remain available.
On a miss, the target runs pytest and saves `junit.xml` under its output.
On a hit, Nix reuses the successful output; no pytest process runs. Failed pytest executions fail the derivation.

Keep sandboxing enabled for these builds, including manual invocations. This is
explicit in the recipe and CI configuration because Nix defaults differ by OS.
Sandboxing blocks undeclared checkout inputs; it is not a guarantee against
nondeterminism from clocks or platform behavior. Nix daemon tests remain fresh host executions.

ADR 0004's optional `conformanceNative.fixture`, `conformanceNative.coverage`,
`conformanceCoverage`, and `conformanceDocs` derivations rebuild upstream mining,
source instrumentation, and release requirement evidence separately. They do not
alter the model. See [progress and coverage](../docs/conformance-progress.md).
Hypothesis is an input only to `tests.model` and the development shell.
