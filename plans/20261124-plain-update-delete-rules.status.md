# Exact steps for plain UPDATE and DELETE

Created 2026-11-24. Status OPEN.

[Task](20261124-plain-update-delete-rules.task.md) ·
[ADR 0033, D1–D11](../docs/adr/adr-0033-exact-step-rules.md) ·
[Pilot findings](../docs/records/statement-rule-pilot-findings.md)

## Starting revision

Slice 2 starts at fdcec52f, the head of PR #477, above the pilot in PR #476.
The Nix verdict at the starting revision is
`/nix/store/g78s7bipxgqzcmq06rbfmgvcr60jaicn-belay-verdict`.
Its report.json SHA-256 is
`cc8d3a2d6ffedff458ace5d6ce9b947f7feca8cceb176dbc35a3b766c1daf21b`.
Its counts.json SHA-256 is
`d8e2e1502df379445a40ebeb12812d30fbd6fb5c8be1372f295029cabdb90a6b`.

## Progress

2026-11-24. Traced the branches in StatementStep.lean and the send rules in
PlainUpdateStepRule.lean and PlainDeleteStepRule.lean. Both existing send
rules specialize subqueries to the empty list. The new rules cover all
subquery lists. The no-choice theorems in the model cover writes with
RETURNING and write rules too.
