# Execution-condition task status

Date: 2026-10-26. Status: IN PROGRESS; assigned on 2026-10-28.
Audience: the implementation team.
Task: [execution-aware conditions](20261026-preservation-context.task.md).
Specification: [ADR 0025](../docs/adr-0025-compositional-preservation-proofs.md).
Base for design evidence: `6413afe3ff50`.

## Preparation

The owner requested these specifications before assigning implementation.
The contextual experiment derives the two old raw-run and two old surface-run
generic formulas through one induction per executor. Boundary laws cover
composition, stopped suffixes and the additional counter-readiness check.
The shared [design record](20261026-proof-simplification-design.status.md)
holds Nix evidence and independent reviews.

## Design reconciliation history

On 2026-10-27 the owner requested detailed targets. The task now links the
source-checked condition, induction and certificate inventory. Retained transport
and resolver bridges were explicit; implementation had not started then.

Reconciled on 2026-10-27 with main `daa15385`: statement evidence covers all
effects and surface lifting covers every complete execution. Canonical-run
claims follow by membership. `ScriptConditions` now owns the branch-aware
conditions; INSERT SELECT adapters must transport richer input-dependent
conditions to the selected upsert. Historical own-run prototypes do not
constitute acceptance of this updated contract.

Reconciled again on 2026-10-28 with main `3e2212ed`. Preserve the new explicit
FK `.rewrite` conditions when adapting predicates; execution's `sameOutline`
guard alone does not imply selected-parent equality. Implementation was unassigned
at that design checkpoint.

## Implementation assignment

Implement the new production interface, migrate evidence and callers, and
complete the task's acceptance checks. Delete old condition predicates and
parallel traversals. Experiment-only old-formula conversions must not become
production compatibility paths. Coordinate final names with API removal.

Assignment source: `5327d3fa`, integrating reviewed foundations, API removals,
primitive ownership and the native/resolver CI repairs. The API worker takes this
task in a new isolated workspace. It checked the task against its reviewed
`c2796bd8` API head and found the generic contracts, invariant certificates,
resolver bridges, transport facts and singleton-condition consumer intact.

The four `PreservationApiWitnesses*.lean` files are the single exact-formula
migration set. Keep them through final Nix acceptance, then retire redundancy
with their registrations. Foundation/API tasks still await integrated Nix
acceptance; this assignment does not mark them complete.

Assignment commit `a0fba5a0` passed independent Claude review with zero must and
zero should findings (`reviews/20261028T120718Z-a0fba5a0`). Two documentation
findings from the earlier draft were fixed and recorded.

At assignment, pending work was: condition implementation, independent review, current-formula and
focused semantic checks, full Nix acceptance, witness retirement, integration
and push.


## Execution-condition implementation, 2026-10-28

The working source now uses one five-input `StatementCondition` and one
`StatementKeeps` contract over all effects. `RunConditionsWith` reads the actual
position-dependent state clock, visible counters and parameters. Raw readiness
is an ordinary condition; `with_ready` projects it from state support without
identifying raw readiness with counter knowledge.

`ScriptStepCondition` carries successful resolution, the actual selected clock
and state support to its condition. `ScriptConditionsWith` guards each reached
head obligation with the state invariant and follows every continuing execution.
One all-execution preservation induction handles explicit and derived conditions;
canonical results use membership. The derived helper only constructs guarded
obligations. `runScriptStep_execution_runs` now exposes its already-proved clock
selection equation, which input-dependent clients require.

`RunHoldsReady` and its sole model import/module entry are removed. The
INSERT-query bridge transports the condition at the same five inputs and retains
the selected upsert's readiness implication. Catalog validity, row shape and
distinct-rowid certificates drop their unused readiness hypothesis. Other
admitted certificates retain raw readiness; independent atoms, FK selected-parent
rename premises and unconditional DROP COLUMN claims remain unchanged.
Resolver-derived admission and singleton-script callers use the common interface.

The sole 84-endpoint witness set now uses test-local frozen old predicates.
A signature comparison against assignment base `cf7db8b0` found all 84 complete
formulas unchanged after those predicate-name substitutions. The two shared
helpers, `PreservationContextRaw` and `PreservationContextSurface`, derive the
original generic unconditional/ready and explicit/derived formulas. They have
only the two approved additions to the existing model test inputs. All six
files retire after final context Nix acceptance, together with redundant
foundation migration evidence; there is no production compatibility API.

Lasting checks extend existing owners: `valid_atoms_theorems_test.py` covers
nonzero raw input selection, visible-counter filtering, parameters, false halted
suffixes, distinct raw/state readiness and premise strength. `InsertSelectExecutions`
covers actual input-dependent later obligations after both divergent copy
branches, rejects canonical-only obligations and covers a missing clock's empty
obligation. Existing FK fixtures retain partial FAIL, rollback/saved-snapshot,
open-transaction and selected mapping cases. Axiom audits include the unified
generic proofs and INSERT-query bridge. No new suite or runner was added.

Local diagnostics: targeted generic/model caller builds and the full four-package
`just dev-build` passed (2605 jobs). Seven model/kernel tests passed, including
the 84 endpoints, old generic formulas and input-boundary checks; 25 FK fixtures
and 19 source/docs/layer checks passed. After the final proof edit, the existing surface execution driver and five
model preservation tests passed again (six tests, 23.53 seconds). These results are not Nix
acceptance evidence. Root is running first-batch acceptance separately; final
context acceptance and witness retirement remain pending.


The production package diff removes 143 textual Lean lines, including comments
and blank lines; this is not the goal's non-comment metric. One module and the
parallel readiness/derived preservation proofs are removed. The two temporary
frozen-condition helpers add 179 test lines until retirement. No elaboration
speedup is claimed: targeted/new fixture compilation completes within existing
timeouts, but no controlled before/after cost measurement was made.


## Independent review and integration handoff

Implementation commit: `1773d573bc24108eb033c01de65fe3299ec12288`.
Independent Claude review `reviews/20261028T124835Z-1773d573` reported zero must
and zero should findings, but explicitly omitted central surface proofs and
fixtures. It was treated as incomplete coverage. Supplemental review
`reviews/20261028T125042Z-1773d573` read all changed production proof diffs,
the semantic fixture diffs and both frozen-condition helpers in full, with zero
must and zero should findings. Its remaining partial witness-file coverage was
closed by `reviews/20261028T125314Z-1773d573`, a bounded review of all three changed
endpoint fixtures, also with zero must and zero should findings. These were
read-only reviews; the local compiler/test diagnostics above supplied execution
checks. The review records are retained verbatim.

Source is ready for coordinator integration. Keep this task IN PROGRESS until
final combined Nix acceptance and the required migration-witness retirement.
No source or registration in the isolated acceptance workspace was changed.
