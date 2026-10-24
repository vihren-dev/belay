# Status: queries as sources

Created 2026-10-24. Status: OPEN. Implementation has not started.
Task: [task file](20261024-query-sources.task.md).
Specs: ADR 0019 D5/slice 4 and D3 metadata exception; ADR 0017 S6.
Inspected base: `vihren-dev/sqlite-verifier`, PR #239, commit `98a07bfe`.

## Owner decision and observations

On 2026-10-24 the owner selected: "Support nonrecursive CTEs only; reject actual
recursion and retain the exclusion of the RECURSIVE keyword." The ADR and task
record this scope. There is no outstanding CTE-scope decision.

The prerequisite audit used pinned SQLite 3.51.0 from Nix and observed recursion
without the keyword, ordinary forward CTE references, permitted enclosing-query
references versus rejected sibling references, and CREATE VIEW before a referenced
table exists. These informed the specification, not an implementation acceptance.
Native source and implementation paths are recorded in the task.

The audit found derived-source spellings in 25 corpus-v4 and 180 corpus-v5
records, including 0 and 49 current mustAgree records respectively. These are
lexical counts over setup/schema/migration SQL, not evidence of execution or
measured gains. Views also appear in existing corpora. Implementation must use
actual verdict results and inspect each changed prediction.

## Progress

- 2026-10-24: specified all of D5 in three acceptance parts, including D3's
  compound metadata exception and the accepted semantic recursion exclusion.
  No Nix acceptance check has run. Review `20261024T122324Z-cf7aa9a6` completed
  with no must or should findings.
- A separate implementation workspace will start at a clean S4 boundary, with
  ownership reserved for shared model and text files. ALTER/rebuild work waits
  for the final view representation. FK laws must cover new schema statements
  when the two task branches are integrated.
