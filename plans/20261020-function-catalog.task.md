# The function catalog, text and type functions, and LIKE and GLOB (ADR 0015, slice 1)

Created 2026-10-20. Status: open.
Status file: [status](20261020-function-catalog.status.md).
Specification: [ADR 0015](../docs/adr-0015-functions.md), D1, D2 and D3.

## Process

The whole ADR is built as local jj commits, and the pull requests come at the end of the
ADR (owner decision of 2026-10-20). Each commit runs the tests that touch it. The end of
the slice runs the local verdict, records the corpus, and runs `just test-full`.

## Outcome

1. **Catalog.** Resolution knows each built-in function of the pinned library (141 names)
   with the numbers of arguments it accepts, as `PRAGMA function_list` gives them.
   - A call of a name that is no function is SQLite's prepare error `no such function: X`.
   - A call with a number of arguments that the function does not accept is `wrong number
     of arguments to function X()`, with the name as written.
   - Both come after the errors of the arguments, as in SQLite: `nosuch(nocol)` is `no such
     column: nocol`.
   - A function of the catalog that the model does not describe stays
     `unmodeled-function`, and its message names the function.
2. **Scalar form.** The new functions resolve to one form, `Resolved.Expr.scalar` with a
   `ScalarFunction`. Evaluation gives the value and the fault of each call.
3. **Functions.** `typeof`, `length`, `octet_length`, `lower`, `upper`, `substr`,
   `substring`, `instr`, `replace`, `trim`, `ltrim`, `rtrim`, `hex`, `unhex`, `quote`,
   `char`, `unicode`, `unistr`, `unistr_quote`, `concat`, `concat_ws`, `ifnull`, `nullif`,
   `iif`, `if`, `likely`, `unlikely`, `likelihood`, scalar `min` and `max`, `abs`, `sign`,
   `zeroblob`, `like` and `glob`. Each follows
   SQLite 3.51.0's `func.c`, checked natively, including:
   - text counted in UTF-8 characters by lead bytes, a BLOB in bytes, and numbers as their
     text;
   - `lower` and `upper` on ASCII letters only;
   - `abs` of a text value as a REAL (`abs('-3')` is `3.0`), and `abs` of the smallest
     integer fails with `integer overflow` while the statement runs;
   - `iif` and `if` with two or more arguments, as pairs of a condition and a value with an
     optional last value;
   - scalar `min` and `max` under the collation of the left-most argument that has one,
     and NULL when an argument is NULL;
   - `likelihood` with a second argument that is not a constant between 0.0 and 1.0 is a
     prepare error.
4. **LIKE and GLOB.** The operators `LIKE`, `NOT LIKE`, `GLOB` and `NOT GLOB`, with an
   optional `ESCAPE`, are calls of `like` and `glob` with the pattern first, as SQLite's
   parser makes them, and `NOT` around the call. `LIKE` ignores ASCII case only, `GLOB`
   has `*`, `?` and `[...]` with `^` for a negated class, and an `ESCAPE` of more than one
   character fails while the statement runs.
5. **Where calls can be.** Calls are admitted wherever the model resolves query
   expressions today: result columns, WHERE, ORDER BY, VALUES, SET, RETURNING, index keys
   and filters, CHECK constraints and generated columns. The restrictions that each place
   has for functions stay (for example a date or JSON function in a CHECK).

   (Amended 2026-10-20: `sqlite_version` and `sqlite_source_id` stay `unmodeled-function`,
   because expression resolution has no profile to give the release; they wait for a slice
   that gives it one. They appear in no clean case of the measurement.)

## Tests

- Lean examples of each function, of the catalog errors and of the LIKE and GLOB rules.
- A test that compares the Lean catalog with `PRAGMA function_list` of the pinned library.
- An authored corpus (`conformance/authored_text_functions.py`) of these functions, each
  case with a kernel proof, recorded as a new corpus.
- The verdict of every corpus: the cases that newly agree, none that leave AGREE.
- Mutants: `length` that counts bytes in text, `lower` that changes non-ASCII letters, and
  `LIKE` that compares case, each killed by an authored case.

## Key points

- **Files.** Frontend `belay/sqlite/syntax_queries.py` (`function_call`, `query_expression`;
  `like(` parses as `LIKE_KW LP`). Lean `Resolution/Calls.lean`, `Resolution/ExprForms.lean`
  (`callIssue`, `pairIssue`), `Resolution/QueryExprs.lean` (`resolveOperand`),
  `Resolution/ResolvedExprForm.lean`, `ExprEval.lean`.
- **Every match on `Resolved.Expr`** gets the new constructor: `ExprAny`, reads, date and
  JSON predicates, and the example files.
- **Kernel.** The functions use structural recursion over byte lists, and REAL values only
  through the operations that the kernel reduces (ADR 0015, Context).
- **Faults.** A run-time failure of a function is a `must` fault, as a JSON failure is; the
  harness compares the result code and the phase, which are the same.
- **Reference.** SQLite 3.51.0's amalgamation (`sqlite3.c`, `func.c` part) is the source of
  each rule; each rule is checked natively.
