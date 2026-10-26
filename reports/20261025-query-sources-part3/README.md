# View-part prediction classification

Date: 2026-10-25. Task: `plans/20261024-query-sources.task.md`, part 3 (views).
The overall status is in [the task status](../../plans/20261024-query-sources.status.md).

## Comparison

- Baseline: the accepted CTE predictions,
  `/nix/store/wbpwn1x38fyn3l0g00wg5m011n6ajwq4-sqlite-verifier-predictions`.
- Result: the view-part predictions after review round 2 (CREATE VIEW, DROP VIEW,
  `table_info` and write errors),
  `/nix/store/bi8dvn7zxjwgrcn0mggw7zy5jpq8ay3m-sqlite-verifier-predictions`.
- The final v53 predictions,
  `/nix/store/cdglbidddydm09iw1i5hc7bdl2m51b0f-sqlite-verifier-predictions`, differ from
  the result only in `corpus-v53.jsonl` (checked with `cmp` on all 53 files). The v53 file
  grows from 42 to 178 cases; its first 42 records are unchanged.
- All 53 files and 7,372 cases were compared. 48 files are byte-identical. 402 records in
  five files (corpus v1 to v5) differ. Every previously predicted record is unchanged:
  all 402 records had raw status `unsupported` before.
- The verdicts are computed with `judge.compare.case_verdict` on the frozen corpus records.

| Classification | Cases |
| --- | ---: |
| View DDL newly predicted, verdict AGREE | 93 |
| View DDL newly predicted; the prediction declares itself out of scope (MODEL_UNSUPPORTED) | 4 |
| Still unsupported; only the reason or restriction changes | 305 |

The 4 out-of-scope predictions are `altertab2-8.1` and `altertab2-8.3`, each in corpus v4 and v5.
The 305 records move past the view DDL to their next restriction: 145 stop at the `cmd` form,
32 only gain CREATE VIEW and DROP VIEW in the list of modeled statements, 25 query
`sqlite_schema`, 21 stop at `oneselect`, 18 use an aggregate with ORDER BY, FILTER or OVER,
14 use `INSTEAD OF` triggers, 14 use a result column alias, 10 use RECURSIVE, 10 use a command
wrapper, 6 use another FROM source, and 10 others. [The table](prediction-changes.tsv) lists every changed
record with its before and after status and verdict.

## Claims

Measured gain: 93 new agreements (4,869 to 4,962 over the 7,372 cases of the 53 earlier
files). No current `mustAgree` claim is lost. The claimed gain of corpus v53 is separate: it
holds 158 agreements, listed in `judge/claims.json`.
