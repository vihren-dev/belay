# Exact steps for writes with rules or RETURNING

Created 2026-11-24. Status OPEN.

[Task](20261124-write-mode-rules.task.md) ·
[ADR 0033](../docs/adr/adr-0033-exact-step-rules.md)

The first kind under owner decision 2 is INSERT with write rules. Its
success uses the key run's changes or its written rows, and its failure
takes the same transaction path as the other writes. The model's support
check combines the plain-write checks with the key run's readiness.

## First INSERT with write rules

Measured before implementing another slice 7 kind. The no-RETURNING
equation in InsertWithRules.lean has 67 scc code lines, its model import
adds one, and InsertWithRulesClaim.lean adds 18 client lines. The latter
checks both output cases on an arbitrary valid database and modeled send.
There are no new surface declarations, projections or tactic branches.
The selected Lean tree goes from 99,064 to 99,150 lines (+86), including
59,460 to 59,528 model and 21,558 to 21,576 tests. The pytest registration,
build declarations and plan prose are outside the simplification counter.
