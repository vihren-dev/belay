# Replay immediate transactions on a single connection

Created 2026-11-17. Issue [#343](https://github.com/vihren-dev/belay/issues/343).
Status: open.

Accept the recorded immediate transaction convention in a supported
single-connection profile. BEGIN, BEGIN DEFERRED, BEGIN IMMEDIATE and BEGIN
EXCLUSIVE, each with optional TRANSACTION, must use the existing transaction
snapshot semantics. The certified observations on this connection do not
include lock acquisition. The assumption is an uncontended database.
Read-only access, untrusted schema mode and other writers remain outside
the model. Named transactions keep their own translation restriction.

Replay the eight frozen corpus-v5 cases with transactionMode immediate and
the corresponding corpus-v4 profiles. Each result must agree with SQLite or
name the remaining model restriction. The execution-profile guide, semantic
subset and conformance-format reference must describe the same boundary.
The recorder and frozen observations remain evidence. A change to judge
claims requires a separate owner-approved judge PR.

## Acceptance

Exercise the SQL spellings through translation, including rollback and
commit on an uncontended connection. Check that immediate profiles reach
the model through the recorded-profile path and that the other unsupported
settings still receive their own diagnostics. Use the pinned native replay
and the locked verdict to verify the frozen cases. Confirm which cases
gain coverage.

## Existing code

Grammar/Writes.lean restricts the parsed BEGIN transaction type.
conformance/profile_scope.py checks the execution profile before translation.
The wire profile already validates the immediate and deferred conventions.
The model's begin statement saves the transaction snapshot.
