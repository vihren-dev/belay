# S7 proof costs: collector feasibility and measurement contract

Created 2026-10-24. Status: OPEN. Implementation follows task review.
Status: [progress](20261024-s7-proof-cost-prototype.status.md).
Spec: [ADR 0017](../docs/adr-0017-user-surface.md), S7's check tool and the
target guide's stable-proof requirement. The owner's ADR17 completion request
includes per-proof heartbeat reports and a configurable CI growth bound.

## Present question

The guide promises `belay-sql-check --costs`, but the current surface has no
collector or persisted measurements. Pinned Lean supplies `withHeartbeats`,
which counts the current computation, not a ready-made per-proof registry.
Declaration elaboration can schedule asynchronous proof work. Timing the return
of a declaration command cannot be assumed to count its completed proof.

This bounded prototype establishes a truthful attribution boundary before the
production task fixes its baseline and CLI contracts. It must not silently
replace "each proof" with only calls to Belay tactics, a whole-module number,
or a zero for proofs that were not measured. No production API is added here.

## Required outcomes

- **A compiling collector experiment has a precise boundary.** Demonstrate a
  viable use of pinned Lean's APIs, or a minimal reproducible failure, to obtain
  completed heartbeat counts for ordinary named theorem declarations through
  an import and normal compilation. State whether each count includes type
  elaboration, generated auxiliaries, kernel checking or instrumentation. A
  command/declaration count must be named as such, not advertised as proof-only.
- **Asynchronous work is attributed correctly.** A deliberately expensive proof
  after a cheap proof, and the same pair in reverse order, establish that work
  is not lost or charged to a neighboring declaration. Exercise native async
  settings and a synchronous comparison. If reliable attribution requires
  disabling async, wrapping syntax or changing Lean, report that tradeoff with
  options; do not adopt it as an unrecorded production requirement.
- **Coverage is explicit.** Probe tactic proofs, term proofs, Prop-valued defs,
  anonymous examples, private/namespaced declarations, generated auxiliary
  theorems and proof terms inside a non-Prop declaration. Record which cases
  receive a stable identity and completed measurement, and which do not.
  Failed/cancelled elaborations and missing data are distinguishable from a
  completed zero-cost result. The eventual task must define its public coverage.
- **Units match Lean's budget.** Preserve enough precision to compare costs
  without rounding away growth. Internal heartbeat counts differ by a factor
  of 1000 from user-facing maxHeartbeats units. The report gives the unit and
  exact conversion; the prototype checks that its display/comparison agrees.
- **Imported data is usable.** A small compiled fixture exports measurement
  metadata that a separate process can read without re-elaborating the proof.
  Identify module, qualified declaration or explicit anonymous identity,
  compiler version and measurement scheme. Recompilation replaces that module's
  records; importing it twice does not count its proof twice. Relocation must
  not make a temporary absolute build path the declaration's identity.
- **Measurement does not change the claim.** Instrumented and uninstrumented
  fixtures keep the same declaration types and checked proofs. Normal compiler
  errors remain errors. Record time/heartbeat overhead on a fixed small set of
  actual surface proofs; distinguish an observed overhead from a general bound.
  No admitted proof or native decision is introduced by collection.
- **The design record makes production choices reviewable.** Give measured
  findings, unsupported cases and exact remaining owner decisions. Recommend
  the smallest viable coverage/collection contract. Sketch a deterministic
  baseline comparison using compiler/scheme identity, qualified proof counts
  and an additive user-set growth bound. New, missing and unmeasured entries
  must be reported explicitly; incompatible versions must not be compared as
  a claimed proof regression. This is a proposed contract, not a completed CLI.

## Tests and acceptance

Use isolated Lean/compiler fixtures in the existing Nix surface harness with
finite subprocess timeouts. Test our collector integration and attribution,
not Lean's heartbeat mechanism in isolation. A fixture changes one proof's
work and identifies that declaration's increase; an unchanged fixture keeps
its attribution. Check completed imported records in a second process and
negative cases for unavailable/failed measurements. Do not encode exact counts
that depend on a different compiler or unrelated imported implementation.

Test the proposed pure comparison on unchanged/within-bound and over-bound
measurements, absent entries and mismatched compiler/scheme identity. A real
changed-proof fixture must supply at least one measured growth case. These
checks demonstrate the eventual CI behavior without publishing a baseline
manager, dashboard or general profiling framework.

Each coherent commit has focused checks and independent review. The one task
boundary runs post-review `just test-full` and `just verdict`, then task-end
`just test-nix` and `just test-scheduled-checks`. Only Nix results are acceptance
evidence. Production semantics, frozen predictions and the judge lock stay fixed.

## Existing interfaces and ownership

Pinned Lean 4.34.1 provides `Lean/Util/Heartbeats.lean`, command elaboration and
async elaboration APIs, persistent environment extensions and imported module
metadata. Inspect those APIs rather than assuming profiler wall-clock traces
are proof heartbeat measurements. The native declaration path and background
checker hooks are relevant; reserve shared hooks with S5 before production work.

Own test-only collector/reader fixtures, a bounded Python test driver, one
reserved surface-suite registration and `docs/s7-proof-cost-findings.md`.
Use the installed surface and existing test support. No production surface,
compiler fork, new dependency or public command belongs to this prototype.
Keep modules below 200 lines and document measurement assumptions. Coordinate
with the S7 file/checker owner: production will share its executable, not create
a second check tool. If the promised coverage cannot be achieved with the
native boundary, stop that implementation branch and present the evidence.
