# belay

The surface: the library that Lean developers import, `Belay`, with the SQLite surface under
`Belay.Sqlite` (ADR 0016). It imports the model only through its roots, `Belay.Sqlite.Model`,
`Belay.Sqlite.Model.Codec` and `Belay.Sqlite.Model.Codec.Resolution` (the terms of statement
syntax that `sql r"..."` gives), and reads SQL text with the text package below it,
`packages/belay-sqlite-text`.

The text package calls the SQLite parser library while a file elaborates, so the modules of
both packages are precompiled and linked with the library. Lake reads the library's folder from
the environment variable `BELAY_PARSER_LIBRARY`:

```sh
nix-build build-support/default.nix -A parserLibrary.library --out-link build/parser-library
BELAY_PARSER_LIBRARY=$PWD/build/parser-library lake build Belay Belay:shared
```

Lake loads the precompiled modules for `lake build`, `lake lean FILE` and the editor's server.
`lake env lean FILE` does not load them, and `lean` then stops at the first parser call.

## Programs and runs

A script is SQL text as data: `sql r"..."` gives a `Script`. A program can use the output of a
statement to choose what it sends next. `Sql α` is the type of programs that give a value of type
`α`, and it is a monad:

```lean
def closeAndCount : Sql (Option Value) := do
  sql r"UPDATE invoices SET status = 'closed' WHERE amount = 0"
  single (sql r"SELECT count(*) FROM invoices WHERE status = 'open'")
```

- `Sql.pure v` sends no statement. `Sql.exec statement values rest` sends one statement and
  gives its output to `rest`. All other programs are built from these two.
- `send s : Sql (List Output)` sends each statement of `s`; the value is their outputs.
- `query s : Sql (Except Nat (List (List Value)))` sends a script of exactly one statement; the
  value is its rows, or its error code. For an output `oneOf`, it gives the first result.
- `single s : Sql (Option Value)` sends a script of exactly one statement; the value is the only
  value of a result with one row of one column, and `none` otherwise.
- A script on its own line in a `do` block is sent, and its value is dropped.
- `outputs.allOk` tells whether no output is an error or `Output.unmodeled`.

`Sql` has a `LawfulMonad` instance. `Sql.runFrom_bind` composes runs on the full connection
left by the first program, including its transaction and counters, and at the next statement
index. `send_append` and `Sql.runFrom_send_append` give this composition for two scripts.

`db.run p` runs a program or a script on a database, and `p.run db` (`Sql.run`) is the same run
of a program. A script runs as the program `send s`. The result is a `Run α`:

- `value : Option α`: the program's value, or `none` when a statement gives `Output.unmodeled`
  (the rest of the program does not run);
- `outputs`: one output for each statement that ran;
- `db` and `start`: the valid databases at the end and at the start;
- `transaction`, `foreignKeys` and `recursiveTriggers`: the state of the connection at the end.

The preservation theorem supplies the final database's validity proof. A run preserves the
model's outputs and result fields directly; it does not decide validity at runtime.
`Run.ofValid` also bundles any model result for which the caller supplies this proof.

The last argument of a run is the environment, `env := e`, with `Env.default` when it is not
given. `Env.default` has no clock: a statement that reads the clock, such as
`CURRENT_TIMESTAMP`, gives `Output.unmodeled`. `clockAt "2026-10-20 12:00:00"` gives that time,
in UTC, to every statement; Lean checks the text where it is written. `Env.atTime` takes the time
in Julian-day milliseconds, and `{ clock := some f }` gives the time `f i` to statement `i`.

```lean
example : (start.run (env := clockAt "2026-10-20 12:00:00") do
    single (sql r"SELECT date('now')")).value = some (some (("2026-10-20" : String) : Value)) := by
  decide +kernel
```

A connection also has three counters: the value of `changes()`, `total_changes()` and
`last_insert_rowid()`. The environment gives them at the start of the run. `Env.default` knows
none of them: a statement that calls a counter function before a write of the run has set that
counter gives `Output.unmodeled`. `Env.newConnection` gives 0 to each counter, as a new SQLite
connection does. A write sets the counters that it changes, so the next statement can read them.
The fields are independent: `{ Env.newConnection with clock := some f }` has both.

```lean
example : (start.run (env := Env.newConnection) do
    single (sql r"SELECT changes()")).value = some (some (0 : Value)) := by
  decide +kernel
```

`Script.run_env` states that a run in which no statement reads the clock and no statement ends at
a counter that the run does not know is the same in every environment.

## SQL in separate files

`sql_file "sql/schema.sql"` reads a file at compile time and gives the same `Script` as `sql r"..."`
for the same text. The path is relative to the package that owns the Lean file, so the form works
from any folder and after the package moves. Every parameter of the file, including `$name`,
becomes an argument of the definition, in the order of its first appearance:

```lean
def schema := sql_file "sql/schema.sql"
```

- `sql_file "sql/m.sql" (section := "up")` selects one direction of a migration file. The
  `-- +goose Up` and `-- +goose Down` markers and the dbmate `-- migrate:up` and `-- migrate:down`
  markers are known. A file with direction markers needs a section.
- `sql_file "sql/seed.sql" (against := db)` also checks each statement against the database `db`
  and reports the problems at the form. The value of the form does not change.
- `sql_module Queries from "sql/queries.sql"` defines `Queries.name` for each statement that
  follows a `-- name: name` marker. The ordinary comment lines after the marker become the
  docstring, and the docstring ends with the SQL location. A suffix such as `:one` is ignored.
  `(against := db)` works as for `sql_file`.
- A marker or tool syntax inside a string, a comment or a trigger body is ordinary SQL text and
  names nothing.

An external SQL edit is not seen by a Lean file that is already open: restart the Lean file, or
run `lake build`. If the compiler cannot decide which package owns the Lean file, for example
with two nested Lake projects of one name, write `set_option belay.sql.packageRoot ".." in`
before the form. The value is a path relative to the folder of the Lean file.

### Check that a build is fresh

Lake rebuilds a library after an SQL edit only when the lakefile lists the SQL files as inputs
of the library:

```lean
input_dir sqlFiles where
  path := "sql"
  text := true
  filter := .extension "sql"

lean_lib App where
  needs := #[sqlFiles]
```

`lake exe belay-sql-check` compares the SQL files that the compiled libraries of the current
package read with the files on disk. It builds nothing. It prints, for each library, the number
of modules and SQL sources and the number of stale sources, and for each stale source its package,
path, declarations and the `lake build` command. `--library App` checks one library. The exit code
is 0 when all sources are fresh, 1 when a source changed or is missing, and 2 when a library could
not be read, for example because it is not built. Line-ending changes are not edits.

## Claims about every database

`Holds q db` says that every possible result of the query has a row. `Empty q db` says that
all its possible results have no rows. `Fails q db` says that the query gives an error.
An unmodeled query satisfies none of these claims. Use the query-form lemmas, such as
`Holds.iff_selectOne_count`, to express a claim in terms of the catalog and stored rows.
A free database cannot be evaluated with `decide`; supply its schema facts and use the laws.

The `sql_simp` simp set resolves and evaluates common expressions, including parameters,
comparisons, Boolean operators, `BETWEEN`, `COLLATE`, `count(*)` and `sum`. For example,
`simp [sql_simp]` turns a resolved `count(*)` into the length of its group. The aggregate
equations also have `grind` attributes. For a conditional law, use
`simp (disch := assumption) [sql_simp]` when its hypotheses are already available.

For integer and NULL inputs, `sumOf_fails_iff` describes overflow by the first integer
prefix sum outside the 64-bit range. Later integer cancellation does not clear that overflow.
When every prefix fits, `sumOf_value_of_fits` gives NULL for no integer inputs and the exact
integer sum otherwise. These laws require integer or NULL inputs; text and REAL inputs use
the general aggregate equations and SQLite's conversion rules.

`Holds.iff_step`, `Empty.iff_step` and `Fails.iff_step` expose every resolution branch for
any query. `Fails.of_prepareError` covers a missing table or column, and
`Fails.select_body_prepareError` lifts an expression-resolution error without repeating the
statement interpreter. `Script.not_claims_query_of_undescribed` covers a query that may fail
or has an unsupported subquery. Keep those cases in proofs: a row satisfying a filter does
not imply `Holds` if another row can make evaluation fail.

For a scalar call without `FROM`, `resolveStatement_selectNoFrom_columns` admits a resolved
scalar column, including a fallible function. `Holds.iff_noFrom_scalar`,
`Empty.iff_noFrom_scalar` and `Fails.iff_noFrom_scalar` retain the run's fault and the filter.
Thus `SELECT abs(1)` holds, `SELECT abs(-9223372036854775808)` fails, and adding `WHERE 0`
skips that failing projection and makes the result empty, for every database.

`Succeeds program predicate` states that every database satisfying the Lean predicate runs
the program without an error or an output that ends the run. It checks every complete
environment: one that supplies a clock and knows all three counters, at any values. Use
`program succeeds` for the always-true predicate, or `program succeeds where query` for
`Holds query` as the predicate. The query must be one read-only statement.

Success checks the actual continuation and every concrete result listed by `Output.oneOf`.
This matters when a later statement depends on a `LIMIT` query without a fixed order:
the first result can select a successful branch while another result selects a failure.
Raw `Sql.exec` continuations can also distinguish `oneOf` from `rows`, so both are checked.
`Succeeds.allOk` gives the guarantee for the actual public run. `Succeeds.script_iff` says
that scripts need only this output check, because their later statements do not depend on
earlier outputs. `Sql.SucceedsFrom` exposes the same branch predicate for a specific clock,
statement index and connection, including incomplete environments.

For a query, `Script.query_allOk_iff` characterizes the default run: `Fails` is false and
its output does not end the run. `Succeeds.of_query` and `Succeeds.of_holds` turn successful
default observations into universal success. The converse is not required: supplying a
clock can make `CURRENT_TIMESTAMP` succeed although its default observation ends the run.

`Succeeds.iff_createIndex` gives the exact conditions for `CREATE INDEX` and `CREATE UNIQUE
INDEX`: the table exists, both names pass the reserved-name checks, no table or index uses
the new name, the terms and filter resolve, and a unique index has no conflicting rows.
`LiteralData.uniqueRows_of_column_groups` connects a no-duplicate GROUP BY claim to the
column key check. This direction is sufficient: repeated NULLs group together but do not
conflict in a unique index. The grouping and index must use the same collation.

## Check a claim before proving it

`#sql_check P` tries checked proof automation, then searches for a valid database
that refutes `P`. It reports **proved**, **false**, or **unknown**. A false SQL
claim includes the database construction, bindings, environment, model outputs
and a script for pinned SQLite. Unknown gives no evidence about the claim.
The command adds no theorem. For example:

```lean
#sql_check ∀ db : Database, Empty (sql "SELECT 1") db
example : ¬ (∀ db : Database, Empty (sql "SELECT 1") db) := by sql_refute
```

Use `with (schema := db! "CREATE TABLE custom(x);")` to guide inference, or
repeat `(db := candidate)` after `with` for an ordered candidate sequence.
`(env := environment)` supplies the environment; `(input name := value)` supplies
a quantified input, even when its binder is named `schema` or `env`. These inputs
work with both frontends. They are proposals: claim preconditions are checked,
not assumed. The explicit tactic `sql_refute (db := candidate)` checks a supplied
witness independently of search bounds.

| Lean option | Default | Meaning |
| --- | ---: | --- |
| `sql.check` | true | Check SQL theorem statements in the background |
| `sql.checkBudget` | 100000 | Cooperative Lean heartbeat units; zero disables checking |
| `sql.checkRecursionLimit` | 4000 | Finite reduction depth; zero disables checking |
| `sql.checkCandidates` | 128 | Maximum proposals tried, including explicit witnesses |
| `sql.checkMaxRows` | 2 | Maximum generated rows per table |
| `sql.checkRandomSamples` | 4 | Seeded proposals per parameter value |
| `sql.checkSeed` | 0 | Reproducible sampler seed |
| `sql.checkSize` | 2 | Plausible size parameter; fixed-bound SQL draws are size-independent |
| `sql.checkShrinkAttempts` | 16 | Checked shrink attempts; zero keeps the first witness |

Use `set_option sql.checkBudget 500000 in` before a command or tactic for a
larger search. A heartbeat budget is not a wall-clock deadline. Explicit
witnesses come first, then empty/targeted inferred databases and seeded samples
for each parameter value. Expensive data conditions can need a larger budget.

For arbitrary generators, call `Check.check` with `Check.SampleConfig.witnesses`,
or `Check.checkCandidates` with an elaboration-monad callback. `Check.refuteWith`
accepts a custom quantified-input selector. The certificate and replay APIs stay
separate: a programmatic candidate or display record is not itself evidence.
Theorem statements that mention SQL are checked by default, including anonymous
examples and mutual declarations. Only a certified counterexample is an error.
The native editor action appends an independently checked regression example or
proof example. The original false theorem keeps its error until you change it.
Section hypotheses remain premises; the theorem and proof-body assumptions cannot
justify their own check. Set `sql.check false` to keep only explicit checks.
The shared budget includes discovery, all statements in one command, and checking
the offered text. Use a larger budget for a mutual block. Cancellation and resource
exhaustion leave the claim unknown; background diagnostic latency is separate from
ordinary proof elaboration.
An edit to an earlier command cancels a running check. An edit to the checked
command itself discards the result of the old check, which ends within
`sql.checkBudget`.
