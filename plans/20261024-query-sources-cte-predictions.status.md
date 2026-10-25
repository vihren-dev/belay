# Status: CTE frozen-prediction classification

Created 2026-10-24. Part 2 comparison DONE; the overall query-source task is OPEN.
Parent record: [query-source status](20261024-query-sources.status.md).
Reviewed source: `4e8d9b296d63c7acbe302ebd1c54385d203b2b3d`.

## Baseline and result

- Baseline: `/nix/store/ifmznfzpqyd12dxjhr3yp404ljb0dgxy-sqlite-verifier-predictions`.
- Result: `/nix/store/wbpwn1x38fyn3l0g00wg5m011n6ajwq4-sqlite-verifier-predictions`.
- The requested historical baseline, `/nix/store/2kpi159rivfybjqkv2cw7vxh31qpdlbq-sqlite-verifier-predictions`,
  was absent at comparison time. Before this gate, all 53 files and 7,372 cases
  were confirmed byte-identical to the accepted S4 baseline used here. The
  comparison explicitly checked that earlier equivalence record before using it.
  The record and byte-exact baseline copy are retained locally in
  `/home/codex/work/research_notes/Lean model modularity investigation/cte-prediction-baseline-20261024`.
- All 53 files and 7,372 cases were compared: 50 files are byte-identical;
  all 4,895 previously predicted records remain identical. The 71 changed
  records all previously had raw status `unsupported`.
- 69 records remain unsupported, and only their `reason` field changes. Their
  SQL was checked against the more specific remaining syntax boundary below.
  Before CTE support, 49 of the 71 records stopped at generic `select` refusal
  and 22 at blanket WITH refusal.
- Two records become predicted and have final verdict AGREE: v4 and v5 contain
  the same `altertab3-16.1` setup, which creates a trigger with nested and unused
  ordinary WITH clauses. It does not fire the trigger. These gains establish
  preparation support; the authored focused tests cover CTE execution.
- No frozen corpus, claim or judge-lock file changed. After retirement of the
  publication workspace, the raw comparison is retained at
  `/home/codex/work/sqlite-verifier-s4/build/agent-logs/cte-publication/cte-integration-acceptance/query-source-cte-integration-prediction-changes.json`.
  All six accepted outputs have independent roots under
  `/home/codex/work/sqlite-verifier-s4/build/accepted-cte-artifacts`.

## Remaining boundaries

The 13 INSERT SELECT cases still stop at the existing write-source restriction.
The 46 VALUES-query cases stop at `oneselect`; the two `altertab-30.1` records
reach that form inside their setup trigger. The two ALTER RENAME cases stop at
`cmd` after their ordinary-WITH trigger definitions translate. Six cases retain
RECURSIVE-keyword refusal. Two upsert cases stop at `xfullname` for aliased
INSERT targets. These are diagnostic improvements, not newly modeled outcomes.

## Every changed record

| Corpus | Case | Classification |
| --- | --- | --- |
| v3 | `e_blobbytes:e_blobbytes-1.0:0` | INSERT SELECT |
| v3 | `e_changes:1.1.2:2` | INSERT SELECT |
| v3 | `e_changes:1.2.2:14` | INSERT SELECT |
| v3 | `e_changes:2.2:26` | INSERT SELECT |
| v3 | `e_totalchanges:1.1.3:3` | INSERT SELECT |
| v4 | `altertab:altertab-30.1:109` | VALUES query |
| v4 | `altertab3:altertab3-16.1:43` | accepted trigger creation |
| v4 | `altertab3:altertab3-16.2:44` | ALTER RENAME |
| v4 | `e_changes:1.1.2:2` | INSERT SELECT |
| v4 | `e_changes:1.2.2:14` | INSERT SELECT |
| v4 | `e_changes:2.2:26` | INSERT SELECT |
| v4 | `e_totalchanges:1.1.3:3` | INSERT SELECT |
| v4 | `func:func-37.100:15017` | VALUES query |
| v4 | `func:func-37.110:15018` | VALUES query |
| v4 | `func:func-37.120:15019` | VALUES query |
| v5 | `aggnested:aggnested-9.1:38` | VALUES query |
| v5 | `aggorderby:aggorderby-1.1:0` | RECURSIVE keyword |
| v5 | `aggorderby:aggorderby-6.0:16` | VALUES query |
| v5 | `aggorderby:aggorderby-6.1:17` | VALUES query |
| v5 | `aggorderby:aggorderby-7.0:18` | VALUES query |
| v5 | `aggorderby:aggorderby-7.1:19` | VALUES query |
| v5 | `aggorderby:aggorderby-8.0:20` | VALUES query |
| v5 | `aggorderby:aggorderby-8.1:21` | VALUES query |
| v5 | `aggorderby:aggorderby-8.2:22` | VALUES query |
| v5 | `aggorderby:aggorderby-9.0:23` | VALUES query |
| v5 | `aggorderby:aggorderby-9.1:24` | VALUES query |
| v5 | `aggorderby:aggorderby-9.2:25` | VALUES query |
| v5 | `aggorderby:aggorderby-9.3:26` | VALUES query |
| v5 | `altertab:altertab-30.1:109` | VALUES query |
| v5 | `altertab3:altertab3-16.1:43` | accepted trigger creation |
| v5 | `altertab3:altertab3-16.2:44` | ALTER RENAME |
| v5 | `date2:date2-300:8` | RECURSIVE keyword |
| v5 | `delete4:delete4-3.0.2:7` | RECURSIVE keyword |
| v5 | `e_changes:1.1.2:2` | INSERT SELECT |
| v5 | `e_changes:1.2.2:14` | INSERT SELECT |
| v5 | `e_changes:2.2:26` | INSERT SELECT |
| v5 | `e_totalchanges:1.1.3:3` | INSERT SELECT |
| v5 | `func:func-37.100:15017` | VALUES query |
| v5 | `func:func-37.110:15018` | VALUES query |
| v5 | `func:func-37.120:15019` | VALUES query |
| v5 | `func:func-38.100:15020` | VALUES query |
| v5 | `func:func-39.101:15021` | RECURSIVE keyword |
| v5 | `index8:1.0:0` | RECURSIVE keyword |
| v5 | `json101:json101-21.26:247` | VALUES query |
| v5 | `json101:json101-21.27:248` | VALUES query |
| v5 | `json103:json103-100:0` | RECURSIVE keyword |
| v5 | `json501:json501-1.1:0` | VALUES query |
| v5 | `json501:json501-2.1:8` | VALUES query |
| v5 | `json501:json501-3.1:12` | VALUES query |
| v5 | `json501:json501-4.1:16` | VALUES query |
| v5 | `json501:json501-5.1:18` | VALUES query |
| v5 | `json501:json501-8.1:37` | VALUES query |
| v5 | `json501:json501-8.2:38` | VALUES query |
| v5 | `json501:json501-8.3:39` | VALUES query |
| v5 | `json501:json501-8.3:40` | VALUES query |
| v5 | `json501:json501-8.4:41` | VALUES query |
| v5 | `json501:json501-8.5:42` | VALUES query |
| v5 | `json501:json501-8.6:43` | VALUES query |
| v5 | `json501:json501-8.7:44` | VALUES query |
| v5 | `json501:json501-8.8:45` | VALUES query |
| v5 | `json501:json501-8.9:46` | VALUES query |
| v5 | `json501:json501-8.10:47` | VALUES query |
| v5 | `json501:json501-8.11:48` | VALUES query |
| v5 | `json501:json501-9.1:49` | VALUES query |
| v5 | `json501:json501-9.2:50` | VALUES query |
| v5 | `json501:json501-9.3:51` | VALUES query |
| v5 | `json501:json501-9.4:52` | VALUES query |
| v5 | `upsert2:upsert2-200:2` | VALUES query |
| v5 | `upsert2:upsert2-201:3` | aliased INSERT target |
| v5 | `upsert2:upsert2-202:4` | aliased INSERT target |
| v5 | `upsert2:upsert2-210:5` | VALUES query |
