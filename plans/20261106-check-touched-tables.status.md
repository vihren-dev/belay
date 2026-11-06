# Status: `#sql_check` fills only the touched tables

Created: 2026-11-06. Status: DONE (2026-11-06).
Task: [20261106-check-touched-tables.task.md](20261106-check-touched-tables.task.md).
Design: ADR 0031, slice 3 (D4, D7, the consumer-size fixture of D9).
Previous slice: [20261106-check-compiled-screen.status.md](20261106-check-compiled-screen.status.md).

Relevant source files: `packages/belay/Belay/Sqlite/SampleCandidates.lean`,
`SampleDatabases.lean`, `SampleScriptHints.lean`, `CheckSamples.lean`, `CheckDomain.lean`,
`CheckBudget.lean`, `ReplayConstruction.lean`.

## Progress

- 2026-11-06: task and status files.
- 2026-11-06: touched tables and constraint rows (D4). `Sampling.statementTables` names the
  tables of SELECT, INSERT, UPDATE and DELETE from their hints, none for other statements;
  `Sampling.touchedNames` closes them over foreign keys (parents and children), triggers on
  touched tables and touched views. `inferredData` returns them; they are none (every table)
  when the claim has Lean code, an unsupported structure or a script that does not evaluate.
  `Sampling.candidates` empties the untouched tables in every candidate (`onlyTouched`,
  `touchedTargeted`), enumerates contents of the touched tables only, and applies
  `Sampling.constrainedCells` (NOT NULL fallback, parent keys, no repeated keys) to the contents
  and the seeded databases (`touchedDatabase`). Task item 2 is amended: the targeted rows are not
  changed (ADR D3 applies D4 to the contents). Tests: `surface_search_test`
  (`CandidateConstraints.lean`), `surface_check_screen_test`, `surface_check_real_schemas_test`,
  `surface_check_readable_test`, `surface_s6_check_programs_test`,
  `surface_check_default_budget_test`, `surface_sampling_test`, `surface_rebuild_test`,
  `surface_check_command_test`, `surface_counterexample_test`.
- 2026-11-06: review fixes of D4: the parent keys repeat until they settle
  (`settledParentKeys`); its docs say when they cannot; the matches name every constructor;
  `CandidateConstraints.lean` checks `constrainedCells` before validation and CREATE INDEX.
- 2026-11-06: the schema as the domain (D7). `Database.HasCatalog` with its decision;
  `Check.domainSchemas` reads `db.HasCatalog schema` premises through `domainPremises`, the walk
  of `domainDatabases`, which now splits conjunctions and unfolds `Succeeds` (a query name, whose
  body quantifies the database under its predicate). The search uses the first schema when no
  `(schema := …)` is supplied. Task item 3 is amended for the parameter order of the ADR. Tests:
  `surface_check_real_schemas_test` (the claim `catalog`: `HasCatalog altered` in a conjunction,
  without `(schema := …)`, is false; `decide` proves and refutes `HasCatalog`), and the surface
  tests of the D4 entry plus `surface_inference_test` and `surface_automatic_test`.
- 2026-11-06: screening during generation and a candidate share per value (task item 4, ADR D3
  amended). `Sampling.candidates` takes a `stop` test and ends after the first candidate that
  passes it; `visitCandidates` screens in it and, after a rejected certificate, continues after
  that candidate. `firstAccepted` and `screenBatch` are removed. Each value gets an equal share of
  the candidate count that is left. On the consumer-size schema the screen accepts candidate 15
  for the id 1; the kernel certification and the replay take about 4 s each. Before the share,
  the value NULL used the whole count and time limit. A task whose certificate is rejected can
  now generate up to its share again from that position. Tests: the surface tests of the D7
  entry.
- 2026-11-06: review fixes of the streaming change: the screen of the last candidate runs in the
  timed task; the share is `Check.valueShare` and can be zero; `CounterexampleSearchBudget.lean`
  (`valueShares`) checks the stop test, the continuation after a rejected certificate and that
  the value 1 is reached within 200 candidates after NULL (it fails when every value gets the
  whole count). Tests: the surface tests of the D7 entry.
- 2026-11-06: the share tests move to `CandidateShares.lean`
  (`test_search_screens_while_generating_with_a_share_per_value` in `surface_search_test`), with
  a test that the screen of the last candidate stops at the time limit (it times out when that
  screen runs outside the timed task). Tests: `surface_search_test`.
- 2026-11-06: the consumer-size fixture (D9): `tests/surface/CheckConsumerSize.lean` with
  `tests/surface_check_consumer_size_test.py` in `surfaceChecks`. An authored schema of six
  tables with CHECK constraints, foreign keys, eight indexes, five triggers (the delete trigger
  logs into `message_log`, whose CHECK rejects a NULL conversation) and an ALTER TABLE; its data
  are 58,745 nodes (the limit is 65,536). `∀ id, Succeeds (deleteMessage id) (·.HasCatalog
  consumer)` is false at the default options with one message row; native SQLite rebuilds the
  rows with the triggers off and the replay fails with `CHECK constraint failed:
  conversation_id IS NOT NULL`. The same claim with `(db := orphanMessage)`, a `db!`
  counterexample, is false. Tests: `surface_check_consumer_size_test`.
- 2026-11-06: the kernel certifies the empty database of a value only when the screen accepts it
  (ADR D2: the kernel certifies only screened candidates). Before, each value sent the empty
  database to the kernel: the true variant of #316 spent 0.4 to 0.5 s on it. Test:
  `CandidateShares.lean` (`emptyScreened`: a screen that accepts nothing gets no certification).
  Tests: the surface tests of the D7 entry and `surface_check_consumer_size_test`.
- 2026-11-06: acceptance records (D9). Phases at the default options, three runs each of the
  final code of the slice, with the phases as in the Context section of the ADR:
  - #316: proof attempt 14 to 22 ms, screen compilation 14 to 23 ms, candidate search 0.85 to
    1.4 s (one certification, 0.55 to 0.92 s), `replayClaim` 0.36 to 0.53 s (`databaseValue` of
    the witness 41 to 61 ms, `checkedConstruction` 0.11 to 0.15 s), screened shrink 4 to 5 ms;
    total 1.4 to 2.2 s, `false` (ADR: 37.8 s).
  - True variant (`GROUP BY email COLLATE NOCASE`): proof attempt 14 to 27 ms, screen
    compilation 15 to 20 ms, candidate search 0.32 to 0.47 s with no certification; total 0.35
    to 0.52 s, `unknown` (ADR: 23.0 s; slice 2: 0.6 to 1.0 s).
  - Consumer-size claim: proof attempt 11 to 16 ms, screen compilation 16 to 20 ms, candidate
    search 9.0 to 11.3 s (one certification, 3.7 to 4.7 s), `replayClaim` 2.7 to 3.5 s
    (`databaseValue` 0.9 to 1.2 s, `checkedConstruction` 2.9 to 3.4 s), screened shrink 11 to
    18 ms, certification of the shrunk witness 3.2 to 4.2 s; total 18.9 to 23.4 s, `false`.
  Before the empty database was screened, each value sent it to the kernel (four certifications
  for this claim instead of one).
  Defaults measured again with the consumer-size claim: it is `false` with 300 candidates and
  `unknown` with 100; `false` with a time limit of 5,000 ms and `unknown` with 3,500 ms; `false`
  with a budget of 62,000 and `unknown` with 50,000. The defaults do not change: budget 100,000,
  candidates 10,000, time limit 10,000 ms, random samples 4.
- 2026-11-06: end of the slice. The fixture commit no longer adds `tests/surface/setup.json`, a
  file that a local probe run wrote. Nix `just test-full` passed: 1,447 tests in all suites;
  `just verdict` passed. Suite times (slice 2 in parentheses): `surfaceChecks` 30 tests in
  296.4 s (27 in 297.6 s), `surfaceS6` 66 tests in 483.6 s (66 in 581.8 s); the S6 suite varied
  between 546 s and 871 s in slice 2 on this shared machine, so these are records, not a measured
  speed-up. No existing fixture changed its result in this slice. Slice 3 and the task are DONE.
