# `#sql_check` screens candidates with compiled code

Created: 2026-11-06. Status: OPEN.
Design: [ADR 0031](../docs/adr-0031-fast-sql-check.md), slice 2: D2, D3 without D4, D5, D6, D8.
Slice 1 (D1) and the parts of D3 and D6 for #318 are done
([20261105-check-default-budget](20261105-check-default-budget.task.md),
[20261105-check-real-schemas](20261105-check-real-schemas.task.md)). Slice 3 (D4, D7) has its
own task. Audience: the team.

## Observable behavior

The trust rule does not change: `proved` and `false` come only from kernel-checked proofs, and a
`false` result needs a replay that native SQLite runs.

1. **Compiled screen (D2).** For each claim, the checker builds and compiles one screen: a
   function from the inputs that the search chooses, a database and a value of the value pool, to
   `Bool`. It is true when these inputs satisfy each premise and falsify the conclusion. The value
   goes to each quantified `Value` input that has no supplied value, as `fillValueInputs` does.
   The environment and the supplied named inputs are fixed for the check. It follows the binders as `contradictAt` does, and
   compares the actual runs of an equivalence claim as `refuteByActualRun?` does. The checker
   compiles the screen and runs it on the generated candidates. Only a candidate that the screen
   accepts goes to certification, replay and the observation. A caller of the checking API can
   supply its own screen; a screen that accepts every database gives no `false` for a true claim.
2. **Closure rule (D2, D6).** The checker does not compile a screen or data whose closure has a
   constant with `implemented_by` or `extern`, or a `partial` or `unsafe` constant, outside the
   modules of Lean and of this repository's packages.
3. **No screen (owner decision 2).** A claim whose screen cannot be built or compiled is checked
   with its explicit witnesses and the databases that its equality premises name, and the result
   is `unknown` with the reason. The cooperative candidate path (`normalizedData`, the draws of
   `CheckRandom.lean`, `targetedData`) is deleted.
4. **Candidates in order (D3 without D4).** For each value of the value pool: the empty database,
   the targeted databases, then each content of all tables with up to `sql.checkMaxRows` rows in
   each table, fewest rows in total first, each row with one value of the pool in every column
   (`Sampling.uniform`), then the seeded random databases. Compiled code generates them with the
   functions of `Sampling`. `sql.checkCandidates` counts screened candidates.
5. **Time limit (D2, D8).** All compiled work of a check (the screen, the generation and the data)
   runs in its own task. A new option `sql.checkTimeLimit` (milliseconds) bounds it for the whole
   check. At the limit the checker stops waiting and gives `unknown` with the time-limit reason,
   and no error. Cancellation stops the wait.
6. **Compiled data (D6).** `dataValue`, `databaseValue` and `scriptValue` of the checker compute
   with compiled code and keep the kernel check of `expression = toExpr value`. Lean's evaluator
   (`reduce`) no longer computes them. A generated candidate carries its value; its replay and
   text use that value. The data limits of `CheckBudget.lean` are limits on the size of the value,
   with values that hold a schema of the consumer's size (9,561 nodes).
7. **Construction with the triggers off (D6).** A generated candidate on a schema whose source text
   has statements other than CREATE and INSERT, such as ALTER TABLE, is built by the schema's text
   without its INSERTs (the candidate's rows replace the supplied rows), then `.dbconfig enable_trigger off`, one INSERT for each row,
   and `.dbconfig enable_trigger on`. The model validates the text, runs the INSERTs on the
   schema without its triggers, and requires the candidate's rows.
8. **Shrinking by screening (D5).** The shrink proposals are screened; the checker certifies only
   the smallest accepted proposal. It certifies and replays at most two witnesses: the original
   and the shrunk one.
9. **Unknown has a reason.** The text of an `unknown` result gives the reason when it is the time
   limit or a claim without a screen.

## Tests

Each test has a timeout and runs in the suites of the surface checks (`surfaceChecks`,
`surfaceS6`).

- The claim of #316 is `false` at the default budget, with the same text and replay
  (`tests/surface/CounterexampleReadable.lean`), as today.
- The screening primitive with a screen that accepts every database gives no `false` for a true
  claim.
- A claim that uses a fixture constant with `implemented_by` is not screened, gives `unknown` with
  the reason, and its explicit witness still certifies.
- A claim with a slow screen gives `unknown` with the time-limit reason and no error.
- A claim on a schema text with ALTER TABLE and a trigger is `false`; its replay uses
  `.dbconfig enable_trigger off` and gives the failure in native SQLite.
- The fixture of `CounterexampleSearchBudget.lean` checks the compiled data instead of the
  cooperative reduction: an `implemented_by` override does not change a value, an opaque constant
  is not decoded, cancellation stops the wait.
- The existing fixtures of S5 and S6 give the same results. Each fixture whose result changes is a
  capability change: the status file lists it with the reason, and the pull request names it for
  the owner. The status file lists every existing fixture claim whose screen does not compile.

Acceptance records in the status file (records, not test assertions): for the claim of #316 and
its true variant (`GROUP BY email COLLATE NOCASE`), the time of each phase as in the Context
section of the ADR; the time of the surface check suites in `just test-full` before and after;
the defaults of `sql.checkCandidates` and `sql.checkTimeLimit` and the measurements behind them.

## Tricky points

- A screen premise can be used by later binders (dependent types). Build it as `dite` on the
  premise's decision instance, so that its proof is in scope; compiled code erases it.
- `evalExpr` must run in the elaborator (it adds and compiles a declaration). The compiled
  function runs in a dedicated task. A task cannot be stopped: an abandoned task runs to the end
  of its current computation (owner decision 3). Compile a thunk, so that the work starts in the
  task and not at `evalExpr`.
- The screen is compiled once for the claim. The database and the pool value are its arguments;
  the environment and the supplied named inputs are closed terms in its body.
- Kernel certification stays the only judge: a screen that accepts a wrong candidate wastes time,
  and a screen that rejects a counterexample misses it. Neither gives a wrong result.
- The time limit and the reason of `unknown` must survive `attempt`, which restores the
  elaboration state on failure: keep them in a reference, as the audit cache does.
- The existing tests of cooperative cancellation (`CounterexampleSearchBudget.lean`) test code
  that this task deletes; replace them with tests of the compiled path.
- Default values: `sql.checkCandidates` and `sql.checkTimeLimit` come from the measurements; the
  automatic check of a theorem must not keep the editor waiting.
- Slice 3 adds the touched tables, rows that satisfy constraints and `Database.HasCatalog`, and
  the consumer-size fixture of D9, which needs them.
