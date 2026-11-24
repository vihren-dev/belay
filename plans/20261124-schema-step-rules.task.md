# Exact steps for schema changes and prepare errors

Created 2026-11-24. Status OPEN. Audience: implementers and reviewers.

Slice 4 of [ADR 0033](../docs/adr/adr-0033-exact-step-rules.md) covers
CREATE INDEX, CREATE VIEW, CREATE TRIGGER, ADD COLUMN, plain DROP, catalog
rewrite, DROP COLUMN and prepare errors. From the resolution alone, each
registered equation gives all the ending reasons and continuing executions.
An index can refuse existing rows. ADD COLUMN checks its supported default,
target table, populated-table restrictions and column constraints. A rewrite
requires the same outline. Dropping a column requires its model guard.
Prepare errors give their primary error code. Clients can see the output,
resulting database and connection in every continuing case.

Schema/Dispatch/Execution.lean defines the effects. StatementStep.lean adds
the default support check. The validity of an input database can imply a
guard but cannot be an assumption of the rule. A syntax-level conditional
creation may resolve to a no-op or a prepare error as well as a creation.

Every replaced law must remain provable with its starting premises. The
surface fixtures cover all eight kinds on variable databases and include
failure or all-input claims where applicable. Changed examples compile
through the public rules. The slice includes D8 caller migration and D11
measurements, full checks, and byte-for-byte verdict comparison.
