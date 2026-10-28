# Source agreement task status

Date: 2026-10-28. Status: IN PROGRESS; implementation accepted, retirement review and integration pending.
Audience: the implementation team.
Task: [shared query source agreement](20261028-source-agreement.task.md).
Specification: [ADR 0026 D2](../docs/adr-0026-semantic-proof-boundaries.md).
Source baseline: `81163254`; original source formulas match `3e2212ed`.

## Assignment

The owner authorized ADR 0025/0026 implementation on 2026-10-28. This task is
assigned to the primitive/import worker after its integration build. Its source
owners are disjoint from the ADR 0025 API worker and the CI repair worker.
Shared manifests and Nix source registrations require coordinator sequencing.

The inventory has fourteen source helpers and three additional query endpoints.
The two statement-context endpoints are included in the fourteen. Current and
initial origin paths differ in their read adapters; the shared traversal must
retain complete lookup and pragma observations. Existing two-state tests are
the acceptance owner. The implementation below awaits integrated Nix acceptance.

## Progress and evidence

- Assignment: inspected the three current source files, lower read predicates,
  exact target inventory and existing two-state test helper/axiom list.
- Assignment commit `d3b75dfb`: independent Claude review found zero must and
  zero should findings (`reviews/20261028T114133Z-d3b75dfb`). The earlier
  review record covers the draft before its goal link was added.
- Pending: Nix acceptance, temporary
  migration-witness retirement, integration and push.

## Shared source argument

The implementation adds `Source.Agrees`, `Query.Agrees` and one shared proof
chain in `SourceAgreement.lean`. The origin adapters derive agreement from the
unchanged read tests. `Resolution/QueryForm.lean` now owns both query read
predicates. `TwoStateReads.lean` and `TwoStateCurrentLaws.lean` are removed;
`TwoStateStatementLaws.lean` retains its three query endpoint formulas and
uses the common argument. The manifest replaces the two removed module names
with `SourceAgreement`; the model umbrella needs no direct import change.

The seventeen temporary witnesses preserve the original parameter order and
assumptions, including arbitrary nesting depth and correlated outer rows.
The focused current fixture covers optional table presence, equal rows with
unequal shape, a fixed pragma under simultaneous changes to both databases,
a database-dependent check pragma and its unsupported optional result.
The existing axiom audit now names the generic core and both origin adapters.
Native observation, changed-current-database and origin-swap checks remain.
No executable evaluator, accepted SQL, claim, corpus or mutant table changes.

The source inventory links removed owners to the frozen baseline and names the
new current owners. Inspection found no simp, instance or export registrations
on the fourteen removed helpers. Their only direct production consumer was
`TwoStateStatementLaws`; the existing two-state axiom list was the test consumer.

Diagnostic commands for this commit are `just dev-build`, the model-targeted
build, direct Lean elaboration of the three agreement fixtures, and pytest for
`surface_two_state_test.py`, docs, Lean categories and surface layering.
These local checks are not acceptance evidence. The coordinator will run the
required Nix package, documentation, surface, end-of-slice and end-of-task gates
against the integrated revision before this task is marked done.

A separate diagnostic run of `test_nix_test_targets.py` was discarded: its
`source_tree` fixture copies live `.lake` outputs and raced the development
build while `PlainScanProductions.olean` and `.ilean` were being replaced.
That case failed during copying, before its `nix-build` command ran. Its temporary
copy was removed. This is not a D2 acceptance result or a task source change;
the coordinator runs those checks when integrated package work is at rest.

Pending: integrated Nix acceptance, final
source accounting, retirement of redundant migration witnesses with the accepted
revision recorded for replay, and integration/push confirmation.

## Independent review

Implementation commit `10a1ab51bd51fb5de07eeacc9a540a29ad4feb3b` received
zero must findings and two should findings in independent Claude review
`reviews/20261028T120340Z-10a1ab51`. Both findings concerned the dates of
the D2 status changes in the two agreement specifications. The follow-up
records 2026-10-28 as the status-change date and retains each creation date.
The proof implementation did not change. Nix acceptance and witness retirement
remain pending.

The documentation follow-up `bef73db7931d35f361b966ac88eb356d18ad3b4b` received
zero must findings and one should finding in independent Claude review
`reviews/20261028T120510Z-bef73db7`: the pending list still included the finished
implementation review. This status-only correction removes that obsolete item.
All findings from both reviews are resolved; integrated acceptance remains pending.

## Final-contract witness retirement

The coordinator confirmed final affected-contract Nix acceptance at
`53a346e1899f7221c67faa3c6df379862e16edb8` before this retirement.
The accepted formulas remain replayable at that revision; the
[combined acceptance record](20261028-proof-refactor-ci.status.md) records the Nix evidence.
This entry supersedes the earlier pending-acceptance notes.

Both original-formula migration fixtures and their driver entries are retired.
`SourceAgreement.lean` retains source absence, unequal shape, fixed and dependent
pragma cases. One current generic context assertion protects arbitrary depth,
independent of query-list length; it replaces the two origin-specific depth
witnesses. The generic nesting proof uses arbitrary correlated outer rows.
Existing native observation, changed-current, origin-swap and axiom checks remain.

Affected existing check: `surface_two_state_test.py`.

The cleanup removes only temporary fixtures and their inputs. A bounded diagnostic
run checked the six changed Python test owners plus `test_test_ownership.py` and
`docs_test.py`: 34 cases passed. It used independent copies of the coordinator's
compiled libraries with `LEAN_NUM_THREADS=2`; it is not Nix acceptance.
The log is `/tmp/adr25-26-retirement-diagnostics.log`.

Retirement Nix acceptance, independent review, integration and push remain pending.
No production package, execution semantics or capability changes in this cleanup.
