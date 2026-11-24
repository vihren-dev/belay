# Exact steps for UPSERT and INSERT from a query

Created 2026-11-24. Status OPEN. Audience is implementers and reviewers.

Slice 6 of [ADR 0033](../docs/adr/adr-0033-exact-step-rules.md) gives
resolution-only rules for the UPSERT and INSERT from a query modes without
RETURNING and write rules. The clock, counters, target, support, row-by-row
outcomes, change counts and further executions are observable. The retained
results of FAIL and transaction rollback must agree with the model.
The common send rule must reach the continuation of each production.

The copy proof, INSERT SELECT group laws and row-wise data facts live under
Programs/Scripts and Schema/Writes. A caller with a variable RETURNING list
has a wider domain than the slice. The client fixtures must cover both kinds
on variable databases, including refusal or all inputs, with the ordinary
logical axioms. The slice includes D8–D11 evidence, a byte-for-byte verdict
comparison and the full project checks.
