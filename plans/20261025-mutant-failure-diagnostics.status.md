# Mutation failure diagnostics status

Created 2026-10-25. Status: OPEN.
Task: [required outcomes](20261025-mutant-failure-diagnostics.task.md).

The published #250 hosted log reports three failed groups before outer timeout
exit 124, without final pytest failure details or a general-mutant report
artifact. The task preserves complete successful-run coverage and all existing
limits while making an already reported failure diagnosable. It does not infer
the cause of the query/JSON failures.

Task review is pending. No implementation or acceptance is claimed. The intended
implementation base is published #251, `fe169099`; the view worker will take
this bounded follow-up in an isolated workspace after task review. Two heavy
groups remain reserved for S5 acceptance and migration example checks.
