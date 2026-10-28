# Continuous integration

CI uses Nix to cache builds and expensive hermetic pytest suites. The earlier
[ADR 0001](adr-0001-pytest-and-nix-ci.md) unit-result receipts and coverage
aggregation have been superseded by [Nix test targets](../build-support/README.md).

`.github/workflows/ci.yml` runs the checks on Linux for pull requests.
Pushes to `main`, manual requests and the nightly schedule run
those checks on both native platforms. On pull requests, macOS skips both the
checks and the API reference build.

`tests/ci_scope.py` selects the checks from the files that differ from the pull
request base:

| Scope | Selected when | Recipes |
| --- | --- | --- |
| `docs` | only Markdown documentation and review records changed, including on a `main` push | link checks, no build |
| `test` | any other change | `just test-full` |
| `infrastructure` | build definitions or shared test infrastructure changed | `just test-full test-nix` |
| `full` | the pinned environment, the parser, the workflows or the build entry points changed; other `main` pushes, manual and nightly runs | `just test-full test-nix test-scheduled-checks`, and the `mutants` job |

Every scope checks the review log with `tools/review_log_check.py`. Each review
and each resolution is one file, `reviews/ID/review.json` or
`reviews/ID/resolution-N-SECOND.json`, so parallel branches never change the
same file. Each file must hold a valid record at the path that its record
determines, and each record file of the base commit must be present with the
same bytes. Other files under `reviews/` fail the check. The review statistics
use the date of a resolution to find its latest outcome.

Linux builds the [checked API reference](api-reference.md) for pull requests.
Main, manual and nightly runs build it on both native platforms for
non-documentation scopes. They use the
pinned Nix environment with the checkout's full commit hash for source links.
Only the last, cheap step uses that hash. The expensive base build does not, and
`tools/ci_store_gc.py` keeps it in the saved cache, so a run whose Lean sources
match the cache reuses it.
CI retains `api-reference-SYSTEM` for 14 days, including when a later check
fails. `just documentation-inventory` checks authored Verso coverage.
Documentation dependencies stay outside the conformance runtime.
The complete job has a 75-minute limit. The reference phase keeps its
30-minute limit. The phase that runs the scope's `just` recipes has a 60-minute
limit (`CHECKS_PHASE_LIMIT_SECONDS`). The scheduled mutant suites, which took more than 30 minutes
in that phase, run in the separate job `mutants` instead: one runner per suite, a 75-minute job
limit, and a suite limit of 2700 seconds. Individual compiler and suite deadlines remain
unchanged; a job that reaches its aggregate limit fails.

Each complete check invocation enters the pinned Nix environment once. `tools/ci_checks.py`
checks resources, builds the conformance runtime and
invokes the selected recipe.

`just test-full` builds independent Nix test targets, the suites of `tests`, through
`nix-build -A testReports`. Each suite's output, with its `junit.xml`, is at
`build/nix-tests-full/SUITE`. These are among them; the flake exposes the same
derivations as `checks.<system>`:

- `tests.model`: production SQL translation and concrete Lean model assertions,
  compared with pinned native SQLite on authored and generated cases.
- `tests.coverageStatements` and `tests.coverageFeatures`: the authored coverage cases
  (`tests/conformance_query_coverage_test.py` and `tests/conformance_feature_coverage_test.py`),
  each with a kernel proof of its verdict. They were part of `tests.model`, which took more
  than 1160 s on hosted macOS with them; the three suites now each take about a third of the
  former time.
- `tests.frozen`: replay and classification of the frozen corpora (v1 to v28)
  and checks of the retained evidence reports.
- `tests.corpora`: complete validation of each locked frozen corpus.
- `tests.harness`: fast acquisition, storage, profile and workload checks of the
  conformance harness.
- `tests.sample`: all frozen v4 authored and synthetic cases plus a stable
  upstream sample, with fresh native replay and model classification within
  120 seconds.
- `tests.upstream`: Tcl capture, sampling and import-fidelity checks.
- `tests.parserLibrary`: the in-process parser library: one process with all
  grammars, and, on Linux, the sanitizer job over every parser test input and
  corpus text. Its runtime root holds the built library and inputs, so a model,
  harness or documentation change reuses the result.

`just test-scheduled` builds the scheduled suites of `tests/nix_scheduled_suites.json`
with `nix-build -A scheduledTestReports` (outputs in `build/nix-tests-scheduled/SUITE`).
The `full` scope builds them through `just test-scheduled-checks`, except the mutant suites of
`tests/nix_mutant_suites.json`: the CI job `mutants` runs each of those on its own runner with
`just test-mutants SUITE`, in parallel with the check job, for the `full` scope only, because
together they need more time than the check job has left. A mutant suite's limit is 2700
seconds, since it runs alone on its runner; each test keeps its limit of 300 seconds. The
scheduled suites are:
`scheduledTests.mutants`, `scheduledTests.tableMutants` (writes, joins and table forms) and
`scheduledTests.functionMutants` (the SQL functions of ADR 0015), the mutants of the model, each
built as a changed copy of the Lean packages, where every mutant must change the verdict of
an authored model case; and `scheduledTests.writers`, the round trips of the corpus writers.
Each mutant copy rebuilds the model modules that depend on its change, so the suite grows
with each slice of the model and does not fit the time of a pull request. The `full` scope and the
`mutants` job run these suites, so main pushes,
manual and nightly runs check these suites, and so does a pull request with the
`full` scope. Pull requests with a smaller scope do not, so that their CI time
does not grow. The flake checks exclude them.

- `scheduledTests.writers`: round trips of the corpus writers of the authored cases
  (`conformance/*_evidence.py`): each writes a new corpus, reads it back unchanged
  and replays it natively. The corpora they wrote are frozen, and `tests.frozen` and
  the verdict check them on every pull request.

Each target runs ordinary pytest on a cache miss. Its explicit source files,
Python/pytest, native tools, Lean artifacts and command determine its Nix identity.
Successful outputs retain pytest's JUnit XML. There is no Python cache validator or
coverage-report gate. Nix sandboxing is enabled, with fallback disabled.

Each target declares only the inputs that its tests read. The conformance targets
(`model`, `frozen`, `harness`, `sample` and `upstream`) receive only the SQL frontend
modules listed in `tests/conformance_frontend.json`, so a change to other Python
code, for example under `tools/`, keeps their results.
`tests/test_conformance_frontend.py` checks that list against the actual imports.
Only `tests.frozen` (and the `corpora`, `sample` and `upstream` targets that read them) depend on
the large frozen corpora and retained reports.

While ADR 0010 is implemented, each pull request records its CI job times next to
the latest comparable `main` run, and a big increase (starting threshold: 20 % or
2 minutes for a job) is explained before the merge (ADR 0010 section 11).

The frozen corpora (v1 to v9 and the synthetic workload corpus) are the corpora
that `judge/claims.json` claims, and the judge lock protects their bytes
(ADR 0011, "Verdict of the development claims" below).
`conformance.corpus.load` decodes a locked corpus without validating it again.
Any other directory, such as a copy, a capture or a new freeze, gets the
complete validation (`conformance.corpus.validated_load`). `tests.corpora`
(`tests/conformance_locked_corpora_test.py`) runs the complete validation on
each locked corpus. Its inputs are only the claims, the corpora, the SQL
frontend and the conformance modules that the validation imports, so it runs
again when a corpus changes, which is in the pull request that changes the
judge lock. A module missing from its input list fails it with an import error.

Each test has a 300-second limit (`pytest-timeout`), so a hung test fails with its
own name. The S6 tests that compile a chain of fixture modules have a 600-second limit. Nix runs several targets at the same time, so a target's total time
depends on the other targets; its 1200-second limit only guards against a hang
outside a test. The recipes that build test suites stop `nix-build` after 2700
seconds, so the suite limit ends first and names the suite.
`tests/test_recipe_limits.py` checks this order. They run
`timeout --foreground`, which keeps `nix-build` in the caller's process group, so
the deadline of a CI phase also stops `nix-build`.

The remaining cheap source cases run in one pytest invocation. Cases marked
`requires_nix` (source identities, test-target commands, environment snapshots)
run in `just test-nix`; CI selects it for changes to build
definitions and shared test infrastructure. Tests use trusted repository fixtures; no
sandbox is supplied or tested. Nix daemon tests run on the host.
Cheap unit tests rerun normally. Direct `just test-cases FILE` always executes
pytest, even if the corresponding Nix target is already cached.
Development `just test` selects `developmentTests`, the same targets except
`tests.model`, the two coverage suites, `tests.frozen` and `tests.corpora`. `tests/nix_suites.json` assigns test files to Nix and supplies the
host `--source-checks` exclusion list. Source-owned conformance checks remain
fresh. Every scope from `test` up runs all Nix targets of `tests`.

The pinned cache-nix-action restores the Nix store on every applicable run.
Only main pushes and nightly runs save caches after their checks. The cache key is the platform, the Nix pins and a hash of
every file except `plans/` and `reviews/`. A push that changes only task records
therefore restores the exact store of the earlier push, finds every Nix target
cached and saves nothing. Other runs restore the newest visible matching store for their platform and pins.
Pull requests and manual runs do not save caches. Nix, not the GitHub cache
key, determines which outputs can be reused; changing a declared input creates a
different test derivation.

The check job also substitutes from the publicly readable Vihren Attic cache,
`https://cache.vihren.dev/sqlite-verifier`, trusting only its signing key
`sqlite-verifier:XgeRqTIGBEw3VP8GPrzSvdU+5t1lJz7uEMhIG1lh7QE=` in addition to
cache.nixos.org. Reads need no credentials, so fork pull requests use it too.
`connect-timeout = 5` and `fallback = true` make an unreachable cache or a failed
download fall back to a local build; substitution fallback is unrelated to
`sandbox-fallback`, which stays disabled.

After both native checks of a `main` push or nightly run pass, the
`publish-nix-store` job restores, per platform, exactly the store that the check
job saved and uploads its paths with the pinned Attic client; Attic skips paths
that cache.nixos.org already provides. Only that job uses the `attic-publish`
environment, which deploys only from `main` and holds `ATTIC_WRITE_TOKEN`; pull
request and manual jobs never receive the token. The job may fail or reach
its 60-minute limit without failing the workflow, and it changes no check
result. A missing saved store uploads nothing. The cache, its token rotation and
server operation are maintained in the devops repository
(`docs/vihren-demo/attic-ops.md`). An earlier attempt uploaded inside the check
job and was rolled back ([record](../plans/20260929-attic-ci.status.md)).

Before the save, `tools/ci_store_gc.py` registers garbage-collector roots for the
test targets, the conformance runtime, base API reference (`apiReferenceBase`),
development shell and flake inputs of the current commit, and removes every other
store path. The base API reference and its doc-gen4 build input add about 53 MB
compressed for each platform. Nix keeps the outputs of rooted
derivations' build inputs (`keep-outputs`). Without this step the store kept every
older commit's outputs and grew to 5.8 GB for Linux, while one commit needs about
1.4 GB compressed; GitHub keeps at most 10 GB of caches for a repository, so the
platform caches evicted each other. A path removed by mistake costs a rebuild in a
later run and cannot change a result. The step may fail without failing the job.

Host JUnit reports, cached Nix test outputs and CI phase diagnostics are
retained for 14 days. Pytest's exit status decides success. `tools/ci_checks.py`
writes the output of each phase to the job log while the phase runs, and keeps it in
`build/ci-phases/PHASE/`. After the checks phase, also when it fails,
`tools/test_reports.py` writes a summary to the log and to the job summary page.
For each JUnit report it gives the tests, failures and time, and whether the suite
ran in this job or Nix reused it from an earlier build, by the report's timestamp. It
also lists the ten slowest test cases that ran in this job. Individual subprocess and whole-command deadlines remain
bounded: a timed-out command's process group is killed, and the output read before
the kill is kept, also when a process outside the group keeps the pipes open. The hosted job limit is 75 minutes, including the reference phase, runtime,
complete checks, setup and artifact retention. Child limits
are individual upper bounds; their sum is not a promised job duration. Individual suite and command limits remain unchanged.
Superseded ordinary runs are cancelled; manual and scheduled runs are not.

The matrix follows GitHub's documented native runner architectures:
`ubuntu-22.04` is x64 (`x86_64-linux`), and `macos-14` is Apple Silicon
(`aarch64-darwin`). Each job also checks Nix's actual host system before building.
See [GitHub's hosted runner reference](https://docs.github.com/en/actions/reference/runners/github-hosted-runners).
Runner image updates remain controlled by GitHub; project dependencies are pinned
separately in `nix/flake.lock` and `lean-toolchain`.

Action commits were resolved from official repository tag references on
2026-09-24: `actions/checkout` v6, `cachix/install-nix-action` v31 (an annotated
tag, dereferenced to its commit), and `actions/upload-artifact` v4. The workflow
pins the full commits rather than floating tags. Checkout does not persist
credentials, and the workflow requests read-only repository content permission.

The main ruleset requires `Check (x86_64-linux)` and `Check (aarch64-darwin)`
and requires a branch to be up to date before it merges.

## Verdict of the development claims

The `Verdict` workflow (`.github/workflows/verdict.yml`) runs on every pull
request, including documentation-only ones (ADR 0011). It becomes a required
check of ruleset 23934665 when the owner adds it there after this workflow is
on `main`. It runs
`nix-build integrity/judge.nix -A verdict` and nothing else on its host, and it
restores no GitHub Actions cache.

`integrity/judge.nix` first compares each part of the judge with
`integrity/judge.lock.json`: the judge code and `judge/claims.json`, each claimed
corpus, and the native SQLite oracle (`nix/sqlite.nix` with `nix/flake.lock`).
A changed part stops the job with its name. Then three Nix builds run: the judge
writes the subject's inputs, the subject (`conformance.predict`) predicts from
those inputs in a build without the corpora, and the judge checks the claims.
`verdict-report` keeps the counts and every verdict for 14 days.

`just verdict` builds the same verdict locally. `just judge-lock` prints the
current lock values. A change to the judge, the claims, a corpus or the oracle
updates `integrity/judge.lock.json` in its own pull request, which the owner
approves; `.github/CODEOWNERS` lists the lock, `integrity/judge.nix` and the
workflows.
