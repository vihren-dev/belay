# Query results as bags: integration survey

Audience: the team. Contract:
[task](../../plans/20261128-bag-results-adr.task.md), outcome 5. Measured revision: `18e19a60`
(the code is the same as `main` at `1fb455ac`). The counts come from `rg` over the tracked files
and include references in docstrings. They skip `reviews/`, `reports/`, `build/` and `.lake/`.

`M/` is `packages/belay-sqlite-model/Belay/Sqlite/Model/` and `B/` is
`packages/belay/Belay/Sqlite/`. `.rows` counts only the constructor of `Output` (`.rows x`,
`(.rows _)`, `| rows x =>`), not fields such as `table.rows`. `Answer.rows` in
`M/Queries/Evaluation/GroupExamples.lean` is a different type and is not counted.

## Summary

| Part | Files | Occurrences | What changes |
| --- | ---: | ---: | --- |
| Model package | 75 | 605 | `Output`, the enumeration of results, the laws on them |
| Surface package | 34 | 124 | the claim API that reads rows (`query`, `returnsResult`, `Holds`) |
| Lean tests (`tests/`) | 58 | 239 (`.rows`) | literal expectations and claims on rows |
| Python tests | 13 | | the REPLAY JSON readers and embedded Lean |
| Judge and corpora | 0 | 0 | no change needed (see below) |
| User documentation | 5 | | the text on normal form and on `oneOf` |

The judge already compares a result without ORDER BY and LIMIT as a bag, and a result with
ORDER BY or LIMIT by its native tie groups. The corpora store only native evidence. So the
integration can keep the judge, its lock and the corpora unchanged.

## Model package

1,254 Lean files. 75 files with 605 occurrences.

| Symbol | Occurrences | Files |
| --- | ---: | ---: |
| `.rows` of `Output` | 113 | 43 |
| `oneOf` | 51 | 18 |
| `ofResults` | 74 | 17 |
| `normalForm` | 62 | 30 |
| `possibleResults*` | 125 | 18 |
| `possibleOn` | 36 | 13 |
| `tieGroups`, `groupChoices`, `windowChoices` | 65 | 5–6 each |
| `compareRows`, `compareNormal`, `compareResults` | 41 | 3 each |

By directory (files / occurrences):

- `Queries/Evaluation` (13 / 249): the enumeration and its laws. The largest files are
  `SelectWindowRules` (44), `NormalFormLaws` (30), `PossibleResultsLemmas` (29),
  `SelectProjectionRules` (27) and `PossibleResultsLaws` (25).
- `Programs/Scripts` (27 / 131). Ten files are RETURNING rules of the write statements; each
  makes `.continued (.rows (Resolved.normalForm (returnedRows …)))`.
  `StatementExecution.lean:73` makes one execution for each result of a choice.
- `Programs/Claims` (10 / 68): `QueryOutputs` defines `Output.hasRows`, `hasNoRows` and
  `returnsResult (property : List (List Value) → Prop)`. `QueryOutputOn` makes `outputOn` from
  `Output.ofResults` and `possibleOn`.
- `Tooling/Counterexamples` (6 / 60), `Programs/StatementRunLaws` (11 / 47),
  `Shared/Execution` (2 / 27), `Schema/Dispatch` (4 / 13), `Programs/Clock` (2 / 10).

Theorem statements: 17 mention `Output.rows` or `oneOf`, for example `Output.ofResults_listed`,
`runScriptStep_select_output` and `resolvedStepOutput_select_unordered`. 55 more mention
`possibleResults`, `normalForm`, `ofResults`, `possibleOn` or the tie helpers.

The one law that connects the normal form with permutations is `normalForm_eq_iff_perm`
(`Queries/Evaluation/NormalFormLaws.lean:64`). One test uses it.

## Surface package

320 Lean files. 34 files with 124 occurrences: `.rows` 47 in 20 files, `oneOf` 47 in 22 files,
`possibleResults` 18 in 6 files, `normalForm` 2.

Public declarations whose types read rows as a list:

- `queryResult : Output → Except Nat (List (List Value))`, which gives the first result of a
  choice, and `singleValue`, `query` and `single` (`B/Programs/Claims/ProgramQueries.lean`).
- `Run.returnsResult`, `Run.returnsRows` and their laws (`B/Programs/Claims/RunResults.lean`),
  and `Holds` and `Empty` (`B/Programs/Claims/Queries.lean`).
- `OutputChoice` and its laws, the `oneOf` case of `Succeeds`, `Model.Output.choosesResults`,
  `permittedResults?`, and the text output of each choice in `SqlDocObservation`.
- The bridges from `∀ result ∈ bound.possibleResults …, property result` to claims, for example
  `Run.query_returnsResult_select` and `Sql.check_query_catalog_rows`.

`sql_select` (`B/Queries/Automation/SqlSelect.lean`) works on facts of the form
`result ∈ Resolved.Query.possibleResults …`; its five rules are in
`B/Queries/Automation/SqlSelectRules.lean`. `observationProfile`
(`B/Programs/Reasoning/ExecutionProfile.lean`) is generic in the output type.

## Codec and JSON

- The model codec has no codec for `Output`; it derives JSON for `Value` and `Row` only
  (`M/Frontend/Codecs/Codec.lean`).
- Seven Lean test files under `tests/surface/` copy one `outputJson` function that writes
  `rows` or `oneOf`. Seven Python tests read these rows and compare them as ordered lists with
  native rows; they skip `oneOf`.
- The predictions for the judge carry `StatementOutput` (`columns`, `rows`, `changes`), not
  `Output`. The prediction is the first pass of the model, in the order of `Query.results`.

## Conformance harness and judge

- `judge/outputs.py` `matches_output`: without groups, the predicted rows must be a
  rearrangement of the native rows (a bag comparison). With groups, the rows must follow the
  native tie groups in order, each group as a bag; only the first and the last group can be cut.
- `conformance/native_ordering.py` `query_groups` records groups when the top-level query has
  ORDER BY or LIMIT. A query with a LIMIT inside a subquery stops the capture ("tie structure
  not observable: nested window").
- The second Lean path (`classifyCase`, used by `conformance/model_check.py` and the mutant
  measurement) has the same comparison in `Outputs.lean`, and checks that each possible result
  contains the normalized native rows (`PossibleOutputs.lean`).
- `oneOf` never reaches the judge. `integrity/judge.lock.json` locks the judge and the oracle.
- The corpora: 59 corpora in `judge/claims.json`, 193 `.jsonl.gz` files, 7,868 cases. Events
  store native rows in SQLite's order and, for 867 events in 772 cases, native tie groups
  (40 events have cut groups). No model output is stored.

## Tests

| Location | Files | Literal row expectations |
| --- | ---: | ---: |
| Model package | 12 | 67 |
| Surface package | 3 | 4 |
| Conformance package | 1 | 1 |
| `tests/` (323 Lean files) | 45 | 221 |

In `tests/`, `.rows` occurs 239 times in 58 files, `oneOf` 74 times in 32, `possibleResults`
81 times in 29, and `returnsResult` or `returnsRows` 294 times in 50. 57 theorem statements in
`tests/surface` mention rows or `oneOf`, and 253 mention `returnsResult`, `Holds` or `Empty`.

Python: 7 REPLAY tests (`surface_replay`, `surface_rebuild`, `surface_rebuild_affinity`,
`surface_schema_script`, `surface_derived_column`, `surface_application`, `surface_search`),
2 prediction tests, 2 judge tests, 1 tie-group test, and 4 files with embedded Lean that uses
`oneOf` or `possibleResults`. `conformance/possible_result_mutants.py` patches lines of
`Queries/Evaluation/PossibleResults.lean` by their text.

## User documentation

- `docs/semantic-subset.md`: lines 384 and 702–707 describe the normal form; lines 87–90 and
  102 describe ties in subqueries and windows.
- `packages/belay/README.md`: lines 38–39 (`query` gives the first result of `oneOf`),
  261–262, 301–304 and 326–329.
- `README.md` lines 80–82 and 145, and `docs/guide/agents.md` lines 239–240, show outputs as
  `rows [[…]]`.
- `examples/table-rebuild/TableRebuild.lean` has 2 occurrences.

## Line counts of the code that the bag module can replace

| Code | `wc -l` lines | Code lines |
| --- | ---: | ---: |
| `M/Queries/Evaluation/PossibleResults*.lean` (4 files) | 410 | 240 |
| `M/Shared/Execution/PossibleResults.lean` | 36 | 23 |
| `NormalFormLaws`, `Schema/Dispatch/PossibleResults*`, `PossibleOutput`, two `OutputResultsLaws` | 287 | 168 |
| Total | 733 | 431 |

Code lines are the `Code` field of scc 3.7.0, the counter of the simplification goal, from the
pinned binary of the experiment's Nix build. Files that are mostly about results but have other
content too (`wc -l` lines): `SelectWindowRules` 157, `SelectOrderRules` 150, `StatementExecutionLaws` 125,
`PossibleExecutionsExamples` 107, `SelectOutputShape` 94, `StatementExecution` 76,
`SelectWindowOrderRules` 69.
