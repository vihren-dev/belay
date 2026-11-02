# Observability extraction experiments

Status: experiments complete, 2026-11-02. Audience: the team.
Task: [acceptance criteria](../../plans/20261102-observability-extraction.task.md).

The owner wants continuing evidence about suite growth, overlapping tests,
unnecessary executions and review effectiveness. The constraint is to use normal
tool interfaces. This directory tests extraction, not a ClickHouse service or a
new CI selection policy. All deliberate failures are isolated research fixtures.

[Captured summaries](results.json) retain the tool versions, observations and
immutable Nix output path. The sandboxed target passed, including ten existing
review/report tests with the repository's own conftest. Their ten completion
events match JUnit. The host-Nix test is deselected inside the builder.
The local repeat and Nix-daemon observations are labelled separately.

## Decisions

| Data | Decision | Extraction and limit |
| --- | --- | --- |
| Review findings, resolutions, rule versions | Collect now | Existing JSON records/readers; lossless JSONL round-trip preserves statistics. |
| Review duration/model version | Add at source | Existing records contain neither; historical values remain unknown. |
| Pytest inventory, selection, phases, outcomes | Small integration | Public pytest hooks, explicit plugin loading and JSONL events. |
| JUnit results | Keep | Standard report; a hard process exit can prevent its creation. |
| Python per-test line coverage | Collect on coverage runs | pytest-cov contexts, with documented `core = ctrace` on this Python pin. |
| Python child-process coverage | Collect as unattributed | `patch = subprocess` collects lines, but loses the parent test context in this probe. |
| Lean diagnostics and module imports | Collect now | `lean --json`, `lean --deps`, existing dependency exporter. |
| Lean elaboration profile | Optional artifact | Native `trace.profiler.output`; keep the profile rather than building a profiler parser. |
| Existing Belay proof costs | Consume when present | Existing JSON report; requires opt-in collector, measures body elaboration only. |
| Final proof dependency graph | Consume existing exporter | Compiled declaration type/body references, not proof-search or runtime coverage. |
| Lean runtime paths per test | Defer | Existing source-rewriting markers fail the owner's maintenance criterion; no suitable collector was established by these probes. |
| Nix identities and dependency edges | Collect now | `nix derivation show`, `nix-store` queries, `nix why-depends --derivation`. |
| Nix build/reuse and invocation time | Small wrapper | Link invocation to original test execution ID; time the outer command. |
| Nix exact build/substitution timeline | Defer | `nix build --json` has paths only here; avoid the private `internal-json` protocol. |
| Failed Nix test results | Small builder/log integration | Emit our JSONL records in builder stdout; recover through `nix log`. |
| CI and local provenance | Small wrapper | Allowlisted CI variables and jj commit/change IDs; attach outside derivations. |
| Mutant targets and requirement tags | Export existing data | Static relationships are not measured mutant kills or demonstrated requirements. |

## Reproduce

Use the approved development shell of this workspace (`direnv exec .` if the
caller does not load it automatically). No separate `nix develop` is needed.

```sh
timeout 300 nix-build experiments/observability/default.nix \
  -A probes --out-link build/observability-probes

python3 experiments/observability/nix_probe.py \
  --output build/observability-nix-NEW

nix-build experiments/observability/default.nix \
  -A python --out-link build/observability-python
build/observability-python/bin/python3 experiments/observability/run.py \
  --root . --output build/observability-local-NEW
```

Use a fresh `NEW` directory for each invocation. The first command supplies
sandboxed Nix evidence. The second observes the local Nix daemon; it is not a
GitHub Actions run. The third repeats the integration locally with the same
pinned Python packages. Versions and command output are retained beside summaries.
The CI environment probe uses clearly labelled fixture values, not a live job.

The daemon probe uses a unique seed only to force a fresh experimental build.
Production collection must never pass invocation IDs or timestamps as derivation
inputs: that would invalidate caches on every invocation. Generate an execution
ID inside the builder and attach CI/local invocation identity after retrieval.

## Python observations

The controlled suite has eight parametrized test items. The ordinary invocation
selects seven: three pass, one fails, one errors in setup, one skips, and one
is an expected failure. Hooks expose setup/call/teardown durations, the selected
and deselected IDs, and start/finish events. Setup failure has no call phase.
The collect-only invocation reports selected identities without executing tests.

The abrupt-exit fixture has a start and setup event but neither a finish nor
a JUnit file. A consumer can mark it incomplete; it cannot infer whether it was
a timeout, cancellation or crash from those events alone. The outer process exit
is separate evidence. Closing each JSONL append preserves it across this process
exit, not across a machine failure. Worker crashes, xdist and retry plugins were
not measured. Pytest inventory does not reveal cases hidden inside a Python loop.

Python 3.14.7 with coverage.py 7.15.4 defaults to `sysmon`. With pytest-cov 7.1.0,
it emits `no-sysmon-context` and attributes the nonpositive path to the following
test. This is a documented unsupported combination, not a reason to patch pytest.
Setting `[run] core = ctrace` gives the expected parametrized parent-process
contexts. Subprocess lines still have an empty context. Keep them explicitly
unattributed; do not infer their parent from timing or monkey-patch subprocesses.

Coverage is a periodic measurement with its own mode. These probes establish
extraction and attribution, not production overhead or an optimal frequency.
Import/shared-fixture coverage and empty contexts are not uniquely owned by a test.

## Lean observations

The fixture uses native `decide +kernel`, a named theorem dependency and `#eval`.
`lean --json` gives source positions, severity and diagnostic text. A deliberate
type error returns failure; an admitted proof exposes `sorryAx` through
`#print axioms`. Axiom names remain diagnostic text inside the JSON message, not
a structured list. Reuse the existing Belay axiom audit rather than inventing
a generic parser of all pretty-printed Lean messages.

`lean --profile` provides human-readable cumulative timings on stderr.
`-Dtrace.profiler=true -Dtrace.profiler.threshold=0
-Dtrace.profiler.output=PATH` writes a Firefox-compatible JSON artifact with
elaboration traces. Keep this for occasional investigation; it is not model
branch coverage or a per-theorem kernel-time table.

Lake's `--no-build build Probe` succeeds after a build and after an unrelated
module changes. It exits 3 when an imported module changes, including an unused
declaration added to that module. Module-level invalidation is conservative.
Use `lean --deps` or the exporter's module imports instead of parsing Lake's
progress display or internal trace files.

The existing theorem exporter reads the two compiled fixture modules and finds
the expected reference from `Probe.fromLemma` to `ProbeModel.zero`. Its source
and artifact identities are separate. The graph describes the resulting terms;
it omits discarded tactic searches and changes to the elaboration environment.
It cannot by itself justify skipping proof fixtures.

The existing optional proof-cost collector can be consumed without adding a
second collector. The probe compiles its unchanged source modules, collects one
proof and calls the existing report function. Repeated reads are identical;
editing the source after compilation reports stale data and exits 2. Counts are
internal heartbeats for completed proof-body elaboration, excluding statement
elaboration and kernel checking. The collector already intercepts elaboration
and reads trace structures: do not expand or enable it everywhere for this work.
Prefer ordinary compile invocation times and optional native profiles initially.

## Nix observations

The fixture's relevant input changes its derivation; an unused argument does not.
`nix derivation show` provides the input graph (schema version 4 on Nix 2.34.8).
The documented new Nix CLI is still marked experimental upstream; record its
version and validate the JSON schema. This probe explicitly requires version 4.
`nix why-depends --derivation` explains a path through that graph. Comparing graphs
can identify changed artifacts, but does not directly identify a changed Lean
function or prove that an affected test was unnecessary.

Fresh build and reuse return identical `nix build --json` rows: `drvPath` and
`outputs`. They provide neither a reuse flag nor build timestamps. Cached event
files retain the original execution ID and timestamps. Record an invocation's
reference to that execution; do not insert another copy of its tests as new runs.
An unfamiliar ID can also arrive from a binary cache, so first observation is not
proof of local execution. Exact build/substitution attribution remains unknown.

Deliberately failing and abruptly exiting tests leave invalid Nix output paths;
physical files can remain, so file existence is insufficient. `nix-store
--check-validity` rejects them. Our framed builder events survive in `nix log`.
The fixture forwards its local event file after pytest exits. Killing the entire
builder before forwarding can lose it: this experiment does not solve that case.
Streaming through a documented log path is a later small integration to evaluate,
not a reason to inspect Nix's private daemon events or failed-build directories.

## Initial collection contract and continuing use

The metadata probe exports five existing key-mutant target/guard mappings and
17 authored JSON case records. None of those 17 records has requirement tags.
This is a limited sample, not evidence that the full corpus lacks semantic links.
Static target mappings express intent, not observed detection.

Source inspection found a useful later collection point:
`conformance.resolve_mutants.measure` returns each mutant's `killed` flag and a
`changed` map of case names to changed verdicts. `tests.mutant_sets.measure_set`
currently uses these for assertions. Exporting that result on already scheduled
mutation runs needs a small writer. These experiments did not execute the mutant
suite or establish an all-tests-by-all-mutants matrix; omitted pairs must remain
unknown, not be interpreted as survival.

Keep a host invocation record (UUID, source commit/change, command, CI run/attempt,
job, platform and elapsed time) separate from cacheable execution records.
Use explicit selection reason codes from the existing CI router: requested,
scheduled, scope rule, or unknown. Do not invent a precise reason from coverage.

Store execution ID plus test node ID, event kind, phase, timing and outcome for
pytest. A future retry/worker integration must add an attempt/worker identity
before those executions can be joined safely. Store references from invocations
to artifacts/executions and deduplicate uploaded events. For source/coverage/proof
snapshots retain content identity, tool version, scope and completeness.

Collect small execution/review events on every run. Export static dependencies
and semantic links when their inputs change. Collect Python contexts periodically
on a representative full run; keep Lean profiles on request. Export already
available proof costs without treating a repeated read as new proof checking.

Weekly queries can then report test-count growth, duration trends by comparable
environment, repeated executions of unchanged artifacts, broad dependency
invalidation, incomplete reports, and review outcomes by rule version. Coverage
overlap is advisory and limited to measured Python paths initially. There is no
new safe Lean test selector or automatic redundancy verdict in this result.

Uploads, buffering, ClickHouse ingestion, production overhead, concurrent local
sessions, actual GitHub Actions execution and macOS validation remain deployment
work. No production test behavior or CI selection policy changes here.

## Supported-interface references

- [pytest hooks and report fields](https://docs.pytest.org/en/stable/reference/reference.html)
- [pytest-cov contexts](https://pytest-cov.readthedocs.io/en/latest/contexts.html)
- [coverage cores](https://coverage.readthedocs.io/en/latest/config.html#run-core)
- [subprocess coverage](https://pytest-cov.readthedocs.io/en/latest/subprocess-support.html)
- [Lean compiler CLI](https://lean-lang.org/doc/reference/latest/Interacting-with-Lean/)
- [Lake build dependencies](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)
- [Native trace profile output](https://lean-lang.org/doc/api/Lean/Util/Trace.html)
- [Nix build CLI](https://nix.dev/manual/nix/2.34/command-ref/new-cli/nix3-build)
- [GitHub Actions default variables](https://docs.github.com/en/actions/reference/workflows-and-actions/variables)
