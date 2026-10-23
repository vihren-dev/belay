# Parameters (ADR 0019, slice 1)

Created 2026-10-23. Status: open.
Status file: [status](20261023-parameters.status.md).
Specification: [ADR 0019](../docs/adr-0019-guide-sql.md), D1 (amended 2026-10-23, owner
decision 4), and the order of D7 (amended 2026-10-22): after ADR 0017's S2, before S3.

## Process

As for the slices of ADR 0018: local jj commits with the tests that touch each one; at the end
of the slice the local verdict, the authored corpus with kernel proofs and mutants, and
`just test-full`. Then the slice's pull requests (ADR 0019, owner decision 3): the judge change
that records the authored corpus with its claims and `integrity/judge.lock.json`, which needs
the owner's approval, and the work. The push and the pull requests wait for the owner.

## Outcome

1. **Syntax.** An expression may be a parameter: `?`, `?NNN`, `:name`, `@name` and `$name`, in
   SQLite's token forms (`:1`, `@1`, `:1a`, `$a::b` and `$a(x)` are names). SQLite also takes
   `#name` when the name starts with a letter (`#a`, `#a1`; checked natively), a name apart
   from `:a`; `#` and a digit is a syntax error (`near "#1": syntax error`). `:`, `@` and `$`
   alone are `unrecognized token: ":"` (and the others). Each form that the frontend cannot
   translate stays a frontend refusal.
2. **Numbering.** Each statement numbers its own parameters, as SQLite does. `?NNN` has the
   number NNN (`?01` is 1). `?` has one more than the largest number so far in the statement.
   A name has the number of its first use; its first use gets one more than the largest number
   so far. `:a`, `@a`, `$a` and `#a` are different names. Over `SELECT ?, ?5, ?, :a, @a, $a, :a` the
   numbers are 1, 5, 6, 7, 8, 9, 7. `?0` and a number above the profile's limit (32766) fail
   at prepare with `variable number must be between ?1 and ?32766`; a statement that needs a
   number above the limit for `?` or a name fails with `too many SQL variables`. SQLite gives
   these errors, and the syntax error of `#1`, while it parses, at the first such token, so the
   frontend refuses the script with them (`INPUT_ERROR`, SQLite's message and the token's
   range), as it refuses other text that SQLite's parser rejects.
3. **Values.** A statement runs with one list of values; the value of number N is item N of
   the list (from 1). A number without an item is NULL. A parameter has no affinity and no
   collation, as a literal value: `?1 = '2'` is 0 for the integer 2, and a TEXT column
   compared with `?1` applies its affinity to the value, as with a literal. Each place of an
   expression may hold a parameter: result columns, `WHERE`, `VALUES` cells, `SET`,
   `ON CONFLICT ... DO UPDATE`, `RETURNING`, function arguments, `CASE`, subqueries, `JOIN ...
   ON` and the others that resolution accepts today.
4. **Not a column number.** `ORDER BY ?` and `GROUP BY ?` order and group by the value, a
   constant, also when the value is an integer that names a result column. So `ORDER BY ?1`
   keeps the order of the rows for every value, and `GROUP BY ?1` gives one group when rows
   remain after `WHERE`, and no group when none remain.
5. **LIMIT and OFFSET.** `LIMIT ?` and `OFFSET ?` (alone, not inside a larger expression) take
   the bound value when the statement runs, as SQLite's `OP_MustBeInt` reads it: an integer;
   a real with an integer value (`2.0`); text that numeric affinity makes such a number
   (`'2'`, `' 2 '`, `'+2'`, `'2.0'`, `'1e1'`). Every other value fails the statement with
   `datatype mismatch` (code 20) when it runs: NULL, a blob, `''`, `'abc'`, `'0x10'`, `2.5`,
   `'2.5'`, `1e20` and `'9223372036854775808'`. A negative bound LIMIT has no limit, and a
   negative bound OFFSET skips no rows (checked natively). A literal negative OFFSET keeps
   its restriction. SQLite reads the values when the query starts: LIMIT first, and OFFSET
   only when the LIMIT is not 0. So `LIMIT ? OFFSET ?` bound to 0 and NULL gives no rows and
   no error, while bound to -1 and NULL it fails; a query without rows still reads them
   (`WHERE 0 LIMIT 2 OFFSET ?` bound to NULL fails). A subquery reads its own values only when
   it runs.
6. **Where SQLite refuses a parameter.** At prepare, with SQLite's messages:
   `CREATE TRIGGER` with a parameter anywhere in it (`trigger cannot use variables`);
   `DEFAULT (?)` (`default value of column [x] is not constant`); a `CHECK` constraint
   (`parameters prohibited in CHECK constraints`); a generated column (`parameters prohibited
   in generated columns`); an index expression (`parameters prohibited in index expressions`)
   and the `WHERE` of a partial index (`parameters prohibited in partial index WHERE
   clauses`). `DEFAULT ?` without parentheses is a syntax error (`near "?": syntax error`).
   In the last four places SQLite gives the error while it walks the names of the expression,
   and an earlier error of the walk, such as a name that does not resolve or a misused
   function, can come first or replace it (checked natively). The model gives the parameter's
   error where it is the only error that the walk can find, and the restriction
   `parameter-error-order` for every other expression with a parameter there.
7. **The script and the runs carry the values.** The surface's `Script` carries one list of
   values for each statement; `sql "..."` gives each statement the empty list, and the
   append of two scripts keeps each statement's list. A primitive of the surface gives a
   script's statements their lists, so that S3 can build its syntax over it. The run of
   ADR 0017's S2 (`runScriptFrom`) and the run that halts (`runSqlFrom`) give each statement
   its list; trigger bodies and foreign-key actions read none. Every law over scripts and
   runs (the agreement of the two runs, the states before each statement, the append laws)
   holds for every list of values.
8. **The corpus binds the recorded values.** A corpus case gives the model the values that its
   trace records for each statement (`Case.parameters`); the guards that make such a case
   unsupported (`VerifierConformance/Case.lean`, `conformance/predict.py`) go away.

## Measurement

Over the local verdict after ADR 0017's S2 (2026-10-23), `experiments/model-gaps/next_groups.py`
finds 31 cases of v5 and 12 of v4 that are out of scope and have a parameter; every case with a
parameter is out of scope today. The only forms are `?` and `?NNN`. Of v5, 19 upstream cases
(`triggerE-1.x` and `trigger2-11.2`) put the parameter in a trigger, which SQLite refuses
(outcome 6). The 12 authored cases of v5 (11 of v4) bind a value to each parameter, among them
`LIMIT ? OFFSET ?` in `numeric-ties-windows`. The counts are upper bounds: the cases can use
other forms that stay out of scope.

## Tests

- Lean examples of each outcome, with kernel proofs (`decide +kernel`): the numbering of
  outcome 2, NULL for a number without an item, the affinity examples of outcome 3,
  `ORDER BY ?1` and `GROUP BY ?1` against `ORDER BY 2`, each kind of value of outcome 5, and a
  prepare error of each place of outcome 6.
- Frontend tests of each token form of outcome 1, `#a` included, with the syntax errors.
- An authored corpus (`conformance/authored_parameters.py`), each case with a kernel proof,
  recorded as the next corpus version: the numbering of outcome 2 with distinct values; a
  parameter in each place of outcome 3, also in a write that runs a trigger and in an upsert;
  the affinity and collation examples; `ORDER BY ?` and `GROUP BY ?`; `LIMIT ?` and `OFFSET ?`
  with each kind of value of outcome 5, the errors included, `LIMIT 0` with an OFFSET that
  would fail, and `GROUP BY ?` over no rows; the prepare errors of outcome 6; a script of
  several statements with their own numbers. The refusals of outcome 2 are frontend tests.
- The verdict of every corpus: cases that newly agree and none that leave AGREE.
- Mutants: `?` numbered from the count of earlier parameters, not from the largest number; one
  number for `:a` and `@a`; a parameter with an affinity; `ORDER BY ?` as a column number;
  `LIMIT ?` that accepts a real with a fraction; each killed by an authored case.
- Surface fixtures: a script that binds values runs with them, `sql "..."` binds none, and the
  append keeps the lists (`tests/surface/`).

## Key points

- **Resolution does not know the values.** It keeps a parameter as a resolved expression that
  the evaluation reads from its context (`EvalContext`, `ExprFault.lean`), as `.now` reads the
  clock. Every place that computes a value at resolution must not fold a parameter: the
  constant cells of an INSERT (`constantCell`, `InsertCells.lean`), the assignments
  (`assignedExpression`, `resolveAssignment`, `Assignments.lean`), `integerLiteral` and
  `namedResult` (`QueryTerms.lean`), and `constantDefaultExpression` (`Context.lean`).
  `ClockReads.lean` is the model for a "reads a parameter" check.
- **The window is a constant today.** `Query.limit` and `Query.offset` are numbers fixed at
  resolution (`QueryForm.lean`), read by `Query.results`, `PossibleResults.lean` and
  `Subqueries.lean`. A bound value becomes known only when the statement runs, and it can fail
  the statement.
- **Every builder of an `EvalContext`** must give the statement's values: `EvalContext.plain`,
  `subqueryContext` and `statementContext` (`Subqueries.lean`), and their call sites in
  `StatementStep.lean`, `StatementOutput.lean`, `Execution.lean`, `TriggerRun.lean`,
  `PossibleResults.lean` and `FailingConstraints.lean`. A trigger frame reads no values.
- **Exhaustive matches over `Syntax.Expr`** (`Resolution/SyntaxExpr.lean`) that need the new
  form: `SyntaxEquality`, `SyntaxScope`, `Context`, `ExprForms`, `Collations`,
  `QueryAggregates`, `QueryTerms`, `QueryExprs`, `IndexTerms`, `Returning`, `Defaults`,
  `ReadDefaults` and `FunctionCalls`. No wildcard arms. The codecs are derived.
  `conformance/expression_form_mutants.py` anchors on source text that these edits can move.
- **The frontend.** A parameter is an `expr` node with one `VARIABLE` token
  (`parser/upstream/parse.y`). `Translation/Expressions.lean` refuses it today. The
  action-free grammar accepts `#N` and checks no numbers, so the frontend or resolution must
  give SQLite's errors. The profile has the limit (`Resolution/Profile.lean`,
  `SQLITE_LIMIT_VARIABLE_NUMBER`).
- **The recorder binds every slot.** `conformance/native_bindings.py` requires one value for
  each slot that `sqlite3_bind_parameter_count` reports, so a corpus case cannot leave a
  number unbound. The Lean examples and the native probe in the status file cover outcome 3's
  NULL. `QueryCase` (`authored_queries.py`) has no `parameters` field; `AuthoredCase`
  (`authored_cases.py`) has one.
- **Laws over runs gain an argument.** `ScriptRunLaws.lean`, `ScriptRunStates.lean`,
  `ScriptRunAppend.lean`, `ScriptRunIndex.lean`, `ScriptRunFailure.lean` and the surface's
  `RunLaws.lean` quantify over the connection and the statements; they also quantify over the
  values now. One list for each statement keeps the append of scripts a list append.
- **Checked natively** (3.51.0, typed bindings through `conformance/native_connection.py`):
  the numbering of outcome 2 (`EXPLAIN` slots 1, 5, 6, 7, 8, 9, 7); unbound `?`, `?5` and `:a`
  are NULL; `ORDER BY ?1` with 2 bound keeps the insertion order while `ORDER BY 2` sorts;
  the values of outcome 5; `?32766` is accepted and `?32767`, `?0` and `?32766, ?` fail; the
  messages of outcome 6; a trigger fired by `INSERT INTO p VALUES (?1)` reads `new.a` as the
  bound value.
- **Files.** `Translation/Expressions.lean`, `Resolution/SyntaxExpr.lean`, the resolvers of
  queries and writes, `ExprFault.lean`, `ExprEval.lean`, `Subqueries.lean`,
  `StatementStep.lean`, `ScriptRun.lean`, the surface's `Script.lean`, `Run.lean` and
  `RunLaws.lean`, and the conformance runner (`VerifierConformance/Case.lean`, `Pass.lean`,
  `conformance/predict.py`).
