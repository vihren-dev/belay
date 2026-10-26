# Status: query inserts and ALTER table rebuild

Created 2026-10-24. Status: OPEN. The task was checked against the code on
2026-10-26; no implementation has started.
Task: [task file](20261024-table-rebuild.task.md).
Specs: ADR19 D4/slice 5, ADR17 S6 and ADR22 preservation contracts.

## Accepted decision and prerequisites

On 2026-10-25 the owner accepted possible write executions for plan-dependent
INSERT SELECT behavior. The task and ADR19 now require explicit production
traces and their correlated write states, outputs, errors and counters; public
proofs and conformance must share those alternatives. The pinned optimizer is
not being implemented, and a plan-independent subset is not a substitute.
The existing native rowid/FAIL/ORDER BY probes supply witnesses, not a proof of
complete branch coverage. Review `20261025T015823Z-0088b6d3` of the amendment
had no findings.

The owner accepted exact INSERT SELECT streaming/materialization, including
error precedence and partial writes, on 2026-10-24. ADR19 D4 records the native
overflow-versus-unique-conflict example; the previous always-materialize rule
is superseded. This is a planning/native-source observation, not task acceptance.

The prerequisites have landed: the [query-source task](20261024-query-sources.task.md)
is DONE (2026-10-25), parts 1 and 2 of the
[FK atom task](20261024-foreign-key-atoms.task.md) are accepted, and the
[model name trace](20261025-model-name-trace.task.md) is DONE (2026-10-26). This
task extends those representations and preservation laws. S6's universal
rebuild proof is separate.

## Progress

- 2026-10-24: specified complete D4 scope, three acceptance parts, native
  differential cases and modular contracts. Review `20261024T141909Z-c30f4ce2`
  had no musts and two shoulds. Added the owner cadence override and linked the
  prerequisite tasks. Follow-up review remains.
  No new corpus claim, production source change or acceptance result is claimed.

- 2026-10-26: the workspace `table-rebuild` starts at `4fc773a5` (merged name
  trace), merged with the amendment commit `0088b6d3`, which the base lacked.
  Check of the task against the code and native SQLite 3.51.0, before any
  implementation:
  - Confirmed: the precedence example (rows 2 and 1 stay in `dest` without the
    trigger; integer overflow and no `2` with it); the paired index probes and
    the dead-branch, unused-CTE, UPDATE-only trigger, RETURNING and transfer cases
    of the readiness note (its probe script reproduces them); the file and
    function names of the task; the pinned `parser/upstream/sqlite3.c` (SHA256
    `dc58f0b5`); `Translation/Writes.valueRows` refuses a SELECT source; the
    cadence text agrees with `AGENTS.md`; Valid does not include the FK atoms.
  - Corrected without a change of requirement: the stale prerequisite text, the
    prediction count (55 files, not 53), the superseded owner-choice section of
    the readiness note, and the missing "Starting point" facts (what a catalog
    stores, native rewrite of stored source text, name trace gaps).
  - Open questions, reported to the coordinator and not decided here. (1) Part 1
    holds three changes that each could be a task: the language front end and
    resolution, the exact source production with the insertion fold, and the
    alternatives of a run in the shared statement run, script run, `Sql.Branch`
    and `Output` with the laws of every client. (2) The model syntax does not keep
    the place of the name tokens in stored source text, which the column and
    table renames must rewrite; adding them touches the translator, the syntax
    and its derived instances.
  - Native facts for part 2, verified: `RENAME TO`, `RENAME COLUMN` and
    `DROP COLUMN` leave `changes()`, `total_changes()` and `last_insert_rowid()`
    unchanged; the foreign keys of other tables are rewritten with enforcement
    off; the view output name and the CHECK label are rewritten token by token
    (examples in the task).
  - Name trace gaps for the column rename (planned, to confirm in part 2): a
    view body can be traced as a SELECT statement of its own, which gives exact
    paths. The trigger programs (WHEN condition and body statements with the
    trigger-row scope) need a traced form of `resolveBodyStatement`, so the
    rename closes that gap. CREATE TABLE bodies need no trace, because the
    catalog holds them resolved by position.
  - Plan. Part 1: syntax, text translation, codecs and resolved form of query
    inserts; source production and the insertion fold; the alternatives of a run
    (statement run, script run, `Sql.Branch`, `Output`); preservation laws and
    the narrow query-to-insert contract; conformance membership of complete
    executions; surface forms. Part 2: RENAME TO and RENAME COLUMN with the
    catalog rewrite, the eager validation of views and triggers, rollback, laws
    and conformance. Part 3: DROP COLUMN with the position remap, dependency
    errors, laws, the concrete unsafe and corrected rebuild, documentation.
  - Judge PRs: each part adds authored corpus cases and so needs its own judge
    branch and an owner-approved judge PR (new corpus, claims and lock). The
    conformance classifier is subject code and needs no judge change.
  - Predictions baseline: to build with `nix-build integrity/judge.nix -A
    predictions` on the base before the first model change (not yet built).
  - Review `20261026T091236Z-2957bba7` of the check commit had no findings.
