# Status: S7 proof-cost collector prototype

Created 2026-10-24. Status: OPEN. Test-only implementation is in progress.
Task: [task file](20261024-s7-proof-cost-prototype.task.md).
Spec: ADR17 S7's checker and target stable-proof experience.

## Current evidence

The S7 source audit found no surface collector or compiled proof-cost registry.
Pinned Lean's withHeartbeats counts a computation in internal units, 1000 per
user-facing unit. The experiment now retains native completed body traces and
exports records through a persistent environment extension. The focused Nix
measurement passes; final task acceptance is pending.
No production measurement or baseline guarantee is claimed.

## Progress

- 2026-10-24: specified the bounded attribution/coverage experiment and its
  imported-data and growth checks. Review `20261024T141219Z-2ae528dd` had no
  musts and one should: comparison implementation precedes its settled contract.
  Kept only the written baseline sketch and actual measured-growth fixture.
  Follow-up review 20261024T141307Z-82085ddd had no findings; assignment remains
  pending.
  The production cost task follows the measured findings; files/freshness and
  checked doc blocks remain separate tasks toward the same ADR17 completion.
- Read-only follow-up inspected the pinned Trace/CoreM/MutualDef APIs. Native
  profiler heartbeat mode and named async proof traces are candidate inputs.
  No compiling collector, attribution measurement or imported registry was
  tested. The task now names this evidence without choosing an implementation.
- Review 20261024T153725Z-cca27596 found no musts or shoulds in the additional
  source inputs. The experiment and production cost task remain open.
- Assigned to `s4_part1` in isolated `s7-proof-cost`, based on reviewed S4
  source `2e51a0ae`. S4's broad acceptance remains open; integrate its final
  published boundary before prototype acceptance. Root coordinates those gates.
  This carries the existing task without a new scope decision or task-file edit.
- A read-only preflight identified native `Elab.definition.value` traces as a
  candidate for both sync and async body elaboration. An imported declaration
  wrapper could delegate to `elabDeclaration`, retain completed snapshot/trace
  tasks, and export plain records through a persistent environment extension.
  Its export callback runs after async threads join. No collector has compiled.
- The experiment must enable the trace class to retain exact-zero nodes,
  preserve internal heartbeat units, and flag Float precision loss. Async
  diagnostics can hold consumed traces, so inspect structured messages and
  trace trees. Command linters restore their environment; updates there alone
  do not persist. Body traces exclude headers and later kernel checking, so
  their counts cannot be described as total proof costs. Missing data is not zero.
- Automatic approval rejected shell authorization for the new workspace even
  though its shell files match authorized `s4-run`. Explicit owner approval is
  pending at that checkpoint. Source inspection continued without builds.

- The owner explicitly authorized this and future isolated ADR17 workspaces
  with unchanged approved shell configuration. `direnv allow` succeeded.
  Carry review `20261024T170935Z-905a7bc6` found one citation clarification;
  the task now identifies the private target guide as the cost requirement
  source. The public ADR specifies the check tool. Scope is unchanged.
- Citation follow-up review `20261024T171354Z-d2aa6067` has no musts. Its
  should finding requests access to the private source; the resolution records
  the verified repository, path and published revision. The task already names
  that guide and the owner request, so no further scope edit is needed.
  The reviewed prototype is handed to `s4_part1`; bounded implementation may
  proceed. Root must grant a heavy build slot before broad checks.

## Prototype implementation

- The imported test hook delegates to normal declaration elaboration and keeps
  native body trace snapshots. A separate reader/record module lets the control
  compile use the ordinary elaborator without that hook. The proposed boundary
  excludes headers and later kernel checking; it is named body elaboration.
- Coverage probes include tactic/term proofs, Prop-valued definitions, anonymous
  and private declarations, generated helpers and proofs inside value-producing
  declarations. Generated helpers and embedded proof subterms have no separate
  body records; the design record must retain that limitation.
- The bounded driver checks ordering and actual proof growth, imported records,
  replacement, relocation, failed/missing/cancelled data, exact units, expression
  preservation and the observed overhead of three surface proofs. Native pytest
  suite properties retain the measurements in the Nix result's JUnit report.
- The experiment's surface-suite registration includes its Python helper in
  the Nix fileset. The focused collector check is `tests/proof_cost_test.py`;
  no production package source, prediction or judge lock changes are planned.
- Work paused for the urgent API reference repair and resumed with all prototype
  files and probes preserved. The reference repair is complete. Heavy checks
  were queued at that checkpoint. The focused Nix gate has since passed and
  final S4 source is integrated below. Post-review full tests/verdict, task-end
  checks and publication ancestry remain to be recorded.
- Integrated the immutable final S4 source `24ca8b4c9635ee14f3235001dc86d7315ac514ac`
  as a second parent of the prototype working change. The task handoff ancestry
  and all prototype files are retained. No shared ancestor was rewritten.
  The coordinator owns S4 publication and final acceptance records.
- The record scheme distinguishes native async and synchronous mode. Attribution
  checks compare names and the unchanged theorem's checked expression; they
  record raw repeated counts without requiring exact allocation-count equality.
  The findings document states the coverage gaps and proposed production choices.

## Focused Nix acceptance

- The scoped surface invocation selected all seven `proof_cost` cases and passed
  with no skips (62 other cases deselected), in 39.47s. Report:
  `/nix/store/iq6prjzg44ascwbg6izjvgrg61ic1hww-sqlite-verifier-test-proof-cost-prototype-1`.
  Its JUnit suite properties retain raw attribution, coverage and overhead data.
- Native async and synchronous counts track the expensive theorem in both
  declaration orders. Increasing its real proof work from range 30 to range 100
  increases its measured cost from about 31,765 to about 91,586 internal units.
  The unchanged cheap proof keeps its expression and identity; reordering changes
  its count by 4 async or 6 sync units. Exact count invariance is not promised.
- Nine body records cover the declared fixture categories. Generated helpers and
  embedded proof subterms have no separate body records. Both native-control
  comparisons preserve the exact stored types and proof values. Imported data,
  replacement, relocation, error, cancellation and precision cases pass.
- The three-proof synchronous sample adds 585,850 command-window heartbeats
  (about 9.05%) with collection enabled. The report retains both wall-time samples
  per mode and identifies what each measurement includes. This is an observation,
  not a general overhead bound.
- [Findings](../docs/s7-proof-cost-findings.md) recommend named proof-body
  coverage and record the production coverage, identity and budget choices.
  The prototype does not implement those choices or a baseline comparator.
- Implementation commit `3a09972f59e3313f40306713d350a8e59125029a` passed
  independent review `20261024T184847Z-3a09972f` with no musts and one should.
  The should identifies stale queued-check wording; the historical checkpoint
  now names the completed focused check and the remaining final acceptance.
  The first review response had invalid formatting; its required retry produced
  the valid review above. No implementation finding remains.
- Documentation follow-up `e6acbb3ca188c0943b6df603c1e06dc13f371b90` has no
  musts in review `20261024T184926Z-e6acbb3c`. Its should removes independent
  review from the remaining-items list because that review is now recorded.
  The findings also make native mutual blocks explicitly untested, and recommend
  that production cover ordinary and mutual named proofs, with a focused mutual
  probe before that implementation proceeds. Third-party handlers can remain
  explicit unsupported entries. Collection remains a proposed opt-in facility
  with the guide's user-set additive budget; no numeric default is selected.
- Final findings commit `00a133be7d6a9abec7d96d1d170abb6d85c3695d` has no
  musts in review `20261024T185109Z-00a133be`. Its one should aligns the
  status summary with the proposed named proof-body coverage, including separately
  labeled proof-valued definitions. That wording is fixed in this status record.
  All review findings are resolved; post-review task acceptance is queued.
