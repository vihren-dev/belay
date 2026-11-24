# Exact steps for UPSERT and INSERT from a query

Created 2026-11-24. Status DONE.

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

On the updated query stack (ea83eeff to ff65e488), scc gives 99,400 to
99,722 selected Lean lines. The model changes from 59,216 to 59,492 and
the tests from 22,175 to 22,221. The surface has 14,316 lines, SQL text
1,945, conformance 1,042, public documentation tools 134, other 572.
RowWriteSendClaims elaborates in 5.65 seconds on this stack (faster of
two runs). The CopyStep migration and the new client exercise M03 writes,
M11 execution outcomes, S03 programs and S04 universal claims.

On the final rule-selection code, the D11 total goes from 99,436 to 99,758 lines. The end has 59,492 model, 14,352 surface and 22,221 test lines. The SQL text, conformance, public-doc-tools and other scopes are unchanged.

| Changed sql_run fixture | Start (s) | End (s) |
| --- | ---: | ---: |
| RowWriteSendClaims | new | 3.15 |

Nix accepted the completed slice through `2ac6306b56f8` in `lqc09i2cgak4iy1w69c7w2y10rxnak31-belay-test-reports`. The conformance verdict `73cpz2ka1ri8p1l484crp78ya3gcda3v-belay-verdict` is byte-for-byte identical to the preceding slice’s `g924a0byhr9raapn4krb3kr525773vw4-belay-verdict`. No mutant table changed.
