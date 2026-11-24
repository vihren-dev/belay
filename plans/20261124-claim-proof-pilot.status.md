# Status: pilot of the forms of proof for a claim in SQL

Created 2026-11-24.
Status: OPEN.
Task: [20261124-claim-proof-pilot.task.md](20261124-claim-proof-pilot.task.md).

## References

- Owner request of 2026-11-24 (quoted in the task file).
- ADR 0033, `docs/adr/0033-exact-step-rules.md`: the kind rules that the
  pilot uses.
- `docs/development/lean-simplification-goal.md`: how code lines and
  capabilities are counted.
- Fixtures: `tests/surface/Queries/Evaluation/PurgeFrameQueries.lean`,
  `tests/surface/Schema/Tests/PurgeFrameSite.lean`,
  `tests/surface/Programs/Scripts/PurgeFrameClaims.lean`,
  `tests/surface/Schema/Tests/PurgeFrameInstances.lean`.
- Test: `tests/surface_assertion_examples_test.py`,
  `test_purge_frame_claim_over_every_database`.
- Kind rule: `packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/Scripts/PlainDeleteRule.lean`.
- Two-state assertions:
  `packages/belay/Belay/Sqlite/Programs/Claims/TwoStateAssertions.lean`.

## Branches

| Form | Branch | Starts from |
| --- | --- | --- |
| Base | `claim-proof-pilot` | `adr-0033-phase-8-inventory` |
| A, claims in the logic | `claim-proof-pilot-logic` | base |
| B, composable laws | `claim-proof-pilot-laws` | base |
| C, tactic | `claim-proof-pilot-tactic` | B |
| D, checker | `claim-proof-pilot-checker` | base |

## Progress log

- 2026-11-24: task file and status file written. The task file's
  statements about the present code were checked against the revision
  `adr-0033-phase-8-inventory`.

## Base form

Not started.

## Form A

Not started.

## Form B

Not started.

## Form C

Not started.

## Form D

Not started.
