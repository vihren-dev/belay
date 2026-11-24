# Exact steps for writes with rules or RETURNING

Created 2026-11-24. Status OPEN. Audience is implementers and reviewers.

Slice 7 of [ADR 0033](../docs/adr/adr-0033-exact-step-rules.md) covers every
remaining resolved write. For INSERT, UPSERT, UPDATE, DELETE, INSERT SELECT
and DROP, the kind patterns must be disjoint from the earlier rules and
each other. A modeled write reports its counts or normalized RETURNING
rows on success, and its primary error and resulting connection on failure.
The rules show all clock, counter, support and error cases, including the
effect of foreign keys and triggers and the possible source orders of
INSERT SELECT. Resolution is their only premise.

The pinned model in StatementStep, StatementOutput, InsertSelectRun and
StatementRun.withKeys supplies the behavior. In particular the effect,
written rows and counts of a write with rules come from the same KeyRun.
The status file records the first INSERT-with-rules implementation cost
before any other kind in this slice, as decided by the owner.

Variable-database client claims exercise each kind, covering failures or
all inputs with the permitted axioms. D8 applies to former laws, their
callers and texts, and D5 applies to shared laws after all their kinds have
rules. The end checks include the complete Nix tests, the byte comparison
of verdicts and the fixture timing and line-count records in D11.
