# Exact steps for UPSERT and INSERT from a query

Created 2026-11-24. Status OPEN.

[Task](20261124-row-write-step-rules.task.md) ·
[ADR 0033](../docs/adr/adr-0033-exact-step-rules.md)

Traced the UPSERT summary, support, effects and counts in StatementStep and
the first and further query productions in InsertSelectRun. Read the copy
proof and the group law for variable RETURNING lists.

The UPSERT rule exposes the row summary, counts and FAIL/ROLLBACK state.
The INSERT SELECT rule exposes the table and every production, all support
checks, the main effect, and each alternative's count or error and connection.
CopyStep.lean now derives the compatible-table copy, including every possible
row ordering, from runScriptStep_plainInsertSelect_eq and runStatement_copyOf.
The group laws for variable RETURNING lists remain for slice 7. No former
single-kind law or surface branch was deleted in this slice. RowWriteSendClaims
checks the observed count/error and trace for both kinds.

The review requested that the execution lemma state the modeledness premise
for every further production in its plain-language contract. Added that premise.
RowWriteSendClaims is the only changed sql_run fixture. It is new and elaborated
in 10.05 seconds (lower of two runs). The simplification counter at the first
implementation changed from 98,742 to 99,064, including model 59,184 to 59,460
and tests 21,512 to 21,558. No mutant table changed.
