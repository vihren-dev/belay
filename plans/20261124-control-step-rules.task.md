# Exact steps of transaction control and setting pragmas

Created 2026-11-24. Status OPEN. Audience: implementers and reviewers.

Slice 3 of [ADR 0033](../docs/adr/adr-0033-exact-step-rules.md) gives
BEGIN, COMMIT, ROLLBACK and setting pragmas exact step rules. Resolution
is the only premise. The rules show the primary error code for a repeated
BEGIN and for closing a transaction without a snapshot. A successful BEGIN
saves the database, COMMIT discards the snapshot and ROLLBACK restores it.
A setting pragma installs the value given by resolution. Each step has
one execution. Clients use the common send rule and the registered rules.

The snapshot belongs to the connection state. Resolution determines the
setting value, including the current foreign-key setting inside a transaction.
The transition is defined in Shared/Execution/SqlAdvance.lean. Existing laws
live in ControlStepLaws, ControlStepFrames, PragmaStepLaws, StepContinues and
StepContinuesOk. The send rules and their tactic branches repeat those facts.

Lean must prove every removed statement with its original premises. Client
tests must cover each kind on a variable database, including the failure
or all-input claim for each transaction command. Public and example proofs
that use a replaced law must compile through the common rules. Acceptance
includes the unchanged verdict, full checks, and the start and end code
counts, timing, law and capability records of D11.
