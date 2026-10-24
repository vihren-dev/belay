# S7 proof-cost collector experiment

Audience: designers and reviewers. Status: prototype; focused and full Nix checks pass.
Contract: [task](../plans/20261024-s7-proof-cost-prototype.task.md).
The experiment adds test fixtures. It adds no production command or baseline.

## Measured boundary

The imported hook delegates to Lean 4.34.1's native `elabDeclaration`. It enables
the native `Elab.definition.value` trace and retains the command's proof snapshot
tasks. Export waits for completed snapshots and serializes plain records in the
module's `.olean`. Native asynchronous proof elaboration remains enabled.
The command-return timer is retained only as a diagnostic: it is not the body's
completed cost. Both orderings of a cheap and expensive theorem test attribution.

The precise boundary is **instrumented declaration-body elaboration**:

- Header/type elaboration before the body trace is excluded.
- Term and tactic elaboration, synthesis and checks inside the body region are
  included. Instrumentation that executes inside that region is also included.
- Generated work is included when it runs in that region. There is no separate
  measurement for every generated auxiliary or embedded proof term.
- Later kernel checking and module serialization are excluded. A successful
  body trace alone is not a successful compiler invocation.

Pinned source locations establish the boundary: `Lean/Elab/MutualDef.lean`,
`elabFunValues`; `Lean/Util/Trace.lean`, `withTraceNode`; and
`Lean/Elab/Frontend.lean`, `runFrontend`. The frontend reports completed
snapshots and checks errors before it writes a successful module artifact.
`Pending.finish` also waits for the snapshots it reads.

`IO.getNumHeartbeats` counts small allocations in the current thread. One
user-facing heartbeat budget unit is exactly 1000 internal units
(`Init/System/IO.lean` and `Lean/Util/Heartbeats.lean`). Records retain integers
and declare the unit; display divides by 1000 without rounding. Native trace
endpoints use Float. The collector rejects fractional endpoints or endpoints
above 2^53 - 1, instead of reporting an inexact difference.

## Coverage and identity

| Fixture | Completed body record | Identity and limitation |
| --- | --- | --- |
| Named tactic and term theorems | Yes | Module plus qualified name |
| Definition whose value is a proof | Yes | Definition's qualified name |
| Definition whose value is a proposition | Yes | A declaration-body count, not a proof of that proposition |
| Namespaced and private theorem | Yes | Native qualified/private name; private numbering can change after edits |
| Anonymous examples | Yes | Native example label plus source byte offset; edits can move the identity |
| Recursive theorem's generated helpers | No separate record | The parent body is measured; auxiliary work outside it is not attributed |
| Proof inside a value-producing definition | No separate proof record | The enclosing definition is measured; its generated proof helper is not |

The fixture inventories generated declarations as well as measured bodies. It
compares the exact stored declaration types and values with a compile that uses
the native elaborator without the hook. Discarded anonymous examples have no
stored value to compare; both compilations still check their source proofs.
Collection introduces no admitted proof or native-decision proof axiom.

Failure state belongs to both the record and its compilation. A failed body
trace is marked `failed`; inexact endpoints are `precision-unavailable`.
A successfully compiled module without instrumentation has no records. A
cancelled compiler has no completed output artifact, and its driver reports
the timeout. None of these cases is a completed zero. The explicit zero probe
returns `completed` with integer zero. Production must retain compiler status
and a declaration inventory to distinguish missing coverage from an empty
module; an absent record alone does not explain its cause.

Records identify the compiler version, module, declaration, unit and scheme.
The scheme names this boundary and distinguishes native async from sync mode.
A separate reader imports a fixture after its source is removed. Diamond
imports do not duplicate records. Recompilation replaces that module's records.
Relocating the source preserves record identities without an absolute path.
These identities are suitable for named declarations under a fixed module name;
private and anonymous identities need the caveats above.

## Acceptance measurements

The focused Nix surface gate passed all seven cases, with no skips, in 39.47s.
Its immutable report is
`/nix/store/iq6prjzg44ascwbg6izjvgrg61ic1hww-sqlite-verifier-test-proof-cost-prototype-1`.
`junit.xml` retains the raw `proof_cost.attribution.*`, `proof_cost.coverage` and
`proof_cost.overhead` suite properties. The source includes final S4 boundary
`24ca8b4c9635ee14f3235001dc86d7315ac514ac` and pinned Lean 4.34.1.

| Proof pair | Async cheap / costly | Sync cheap / costly |
| --- | ---: | ---: |
| Range 30, cheap first; three identical compiles | 500 / 31,765 | 502 / 31,766 |
| Range 30, costly first | 496 / 31,742 | 496 / 31,768 |
| Range 100, cheap first | 500 / 91,586 | 502 / 91,580 |

All counts are internal units. For example, 31,765 is exactly 31.765 budget
units. The large proof's real work increase is attributed to that theorem in
both modes. The unchanged cheap theorem retains its exact checked expression,
but reordering changes its count by 4 or 6 internal units. The three identical
compiles agree in this sample; they do not establish general count invariance.
The coverage fixture produces nine body records and exposes three unmeasured
helpers: `Coverage.embedded._proof_1`, `Coverage.recursive._f`, and
`Coverage.recursive.match_1_1`. Imported persistence, replacement, relocation,
failed/missing/cancelled measurements and precision checks all pass.

The overhead sample consists of three maintained surface proof patterns:
constant-query success, default-to-universal success, and default-query success
equivalence. Instrumented and native-control compiles use the same source and
compiler. An initial pair warms imports; four subsequent compiles balance
the mode order. Their common synchronous command window excludes imports and later
serialization. It measures the current thread, not all background kernel work.
Whole-process wall times include imports and export. Neither measure includes
the one-time compilation of the collector itself.

Both measured control windows use 6,474,065 internal units; both instrumented
windows use 7,059,915. The observed increase is 585,850 units, or about 9.05%.
The instrumented body records are 6,871,278 for `constant_success`, 3,687 for
`supplied_success`, and 2,907 for `default_query`. Control wall times are 1.471s
and 1.923s; instrumented times are 1.615s and 1.663s. These small concurrent-host
samples do not establish a general wall-time or heartbeat overhead bound.

The full surface rerun also passes all 69 cases, including the seven prototype
cases, at `/nix/store/fvzkw5nkpb4psc7yp61izi4b533lnxxs-sqlite-verifier-test-surface-1`.
Its JUnit properties reproduce the attribution and window-heartbeat counts.
The unchanged coverage fixture's tactic body measures 3,317 units, versus 3,318
in the focused run: exact cross-run count invariance is unsupported even with
unchanged proof source. The second control wall samples are 1.451s and 1.457s;
instrumented samples are 1.606s and 1.501s. These remain bounded observations.

## Proposed production contract and decisions

The recommended contract reports **completed explicit named proof-body
elaboration**: theorems and separately labeled proof-valued definitions, with
compiler success required before a record is usable. It covers ordinary and
native mutual declarations. Name the instrumented boundary, preserve native
async, retain exact internal units, and report missing/unsupported data.
Ordinary definitions must not be mislabeled as proofs. Anonymous and generated
identities should not silently enter a stable baseline.

The owner must choose whether this explicit declaration coverage meets the
product promise. Literal coverage of every embedded/generated proof requires a
different instrumentation boundary; this prototype does not establish one.
Collection should be optional/configurable, with the guide's additive growth
budget set by the user. The interface must disclose the measured overhead and
count variation. Instrumentation can make a proof near its limit exceed that
limit. Source order and async mode can affect counts; a deterministic comparator
does not make measurements invariant.
Production integration must coordinate the declaration hook with other custom
elaborators, including the S5 checker. This experiment hooks ordinary native
declarations. Native mutual blocks are **untested**: it does not install a hook
for Lean's separate `mutual`-block handler (`Lean/Elab/Declaration.lean`). Start
production work with a focused mutual probe; report an inability to cover this
normal syntax for owner judgment before narrowing the proposed contract.
Arbitrary third-party handlers are also untested and may remain explicit
unsupported/missing entries. The present evidence does not establish every
named declaration form.

Proposed baseline comparison, with no implementation in this prototype:

1. Require compatible compiler, measurement scheme/mode and units. Report
   incompatible records separately; do not call them proof regressions.
2. Match completed named records by module and qualified declaration. Preserve
   raw integer counts and deterministic ordering in the report.
3. Convert the user-set additive allowance to internal units exactly. Report
   growth when `current > baseline + allowance`; never round before comparing.
4. Report new, missing, failed and unmeasured entries explicitly. Do not turn
   them into zeros or update the baseline as part of checking it.
5. Treat a changed module/declaration identity as removed plus new. Report
   private/anonymous identities separately unless the owner accepts their
   edit-sensitive identity policy.

The production task must settle coverage, identity and budget policy from the
Nix evidence before promising `--costs` behavior. No production implementation
is implied by a successful prototype.
