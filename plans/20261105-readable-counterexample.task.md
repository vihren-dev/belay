# A readable counterexample from `#sql_check`

Created: 2026-11-05. Status: DONE (2026-11-05).
Source: issue #316 ("#sql_check prints a counterexample database as a raw Lean structure, twice").
Audience: the team.

## Observable behavior

When `#sql_check`, or the automatic check of a statement, refutes a claim, the message is
one block in this order:

1. `SQL check: false.`
2. The database, when the budget allows its text (the share of the failing observation; a
   certified refutation is reported without it otherwise). `Database:` is followed by one
   table for each table of the catalog: the
   table name, then the column names as a header and one line for each row, as `#sql`
   shows a result (`textTable`). The cells are SQL literals, so `'a'`, `'A'`, `1`, `'1'`,
   `NULL` and `X'00'` are different cells. When the witness database is a named constant,
   the line names it (`Database: sample`). An empty catalog shows `Database: empty`.
   Views, indexes and triggers have no rows and are not shown; the construction script
   has them.
3. The environment, only when it is not the checker's default candidate
   (`Check.candidateEnvironment`): the clock of the first statement as a date and time,
   and the three counters, each as its value or `unknown`.
4. The named inputs and the failing observation, as today.
5. One line for each checked statement with its model output: `uniqueEmail: error 19`.
   The label is the name of the script constant, or the script's SQL text when the script
   is not a named constant. A script with several statements gives one line for each
   statement, with its number. Statements with parameters also give their bindings.
6. Each note of the replays, once.
7. `Construction:` and each different construction script once.
8. `SQLite replay:` and one script for the whole counterexample. When the claim has
   several replays, the script starts each replay after the first with `.open :memory:`,
   so each replay runs on its own new database, as the model's runs do.

Text values in the construction and replay SQL are string literals (`'a'`, `'a''b'`)
when their bytes are valid UTF-8 with no NUL and no carriage return. Other text keeps `CAST(X'..' AS TEXT)`, which
keeps every byte.

The raw Lean structure of the database, `valid := ⋯`, the name `Check.candidateEnvironment`,
`Bindings: [[]]` and the second copy of the construction are no longer printed.

## Tests

- `tests/surface/CounterexampleReplaySource.lean`: `#guard` checks of the literal of a text
  value: ASCII, a quote, non-ASCII UTF-8, a backslash, a line feed, CR LF, NUL and invalid UTF-8;
  `tests/surface_replay_test.py` replays parameters with CR LF, a lone CR, a quote and a backslash.
- A new surface fixture, run by a pytest test, with the claim of issue #316
  (`uniqueEmail succeeds where noDuplicateEmails`). The test checks the whole block of the
  message against the expected text (the tables with `'a'` and `'A'`, no environment line,
  the two statement lines, one construction, one replay), and runs the replay in native
  SQLite 3.51.0: the query gives `1` and the index fails with a UNIQUE constraint error.
- A fixture case with a non-default environment checks the environment line.
- The existing tests that read the message (`tests/surface_check_command_test.py`,
  `tests/surface_s6_check_programs_test.py`, `tests/s6_check_support.py`,
  `tests/surface_s6_not_blocked_test.py`, the editor tests) use the new layout. Their native
  replays still give the same rows; `replays()` splits the one script at `.open :memory:`.

## Tricky points

- The text comes from `Check.describe` (`CheckDisplay.lean`, a `MetaM` function). The
  database and environment values need cooperative evaluation (`databaseValue`,
  `dataValue` in `CheckData.lean`), which is `TermElabM` work under the check budget. The
  check operation (`CheckOperation.lean`) can compute the text with the replays and keep it
  in `Outcome`; the original and the shrunk witness each need it.
- The label of a statement needs the script expression of each query site
  (`replayClaim` in `CheckReplay.lean`); `Replay.Report` today has no label.
- A literal cannot hold a NUL byte, and the shell reads a script by lines, so a CR LF inside a
  literal becomes LF alone (`hex('a\r\nb')` is `610A62` through `.read`); such text keeps the
  CAST. A backslash stays as it is. Construction is validated by `constructionMatches`, so a
  wrong spelling makes the candidate unreplayable instead of wrong; the tests must show that
  the usual witnesses still replay.
- `Replay.valueLiteral` also spells parameter bindings (`bindingsSql`); the change applies
  there too.
- `ReplayDatabaseSql.lean` and the database part of `describe` both walk the catalog with
  the rows by position (`database.raw.rows.getD position []`).
- The issue says that the launch documents and a public checker require the readable lines.
  These are not in this repository; the task covers the output only.
