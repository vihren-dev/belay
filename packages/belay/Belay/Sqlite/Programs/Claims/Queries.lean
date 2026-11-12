import Belay.Sqlite.Programs.Claims.RunResults
import Belay.Sqlite.Schema.Dispatch.Queries

set_option doc.verso true

/-! Queries as propositions over one database (ADR 0017, S2): {lit}`Holds q db`, {lit}`Empty q db`
and {lit}`Fails q db` state what the query {lit}`q` gives on {lit}`db`, for every result that
SQLite may give for it. Each one is decidable, so {lit}`decide` proves it, or its negation, for
a concrete database and query. The query is a script of one read-only statement: the argument
{lit}`query` checks it when the term elaborates, also for a query with parameters. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model Lean Elab Tactic

/-- The output of the first statement of the script on the database, with foreign keys off, as
on a new connection: {lean}`(none : Option Output)` for a script without statements. -/
def Script.outputOn (script : Script) (db : Database) : Option Output :=
  (db.raw.run script).outputs.head?

/-- Whether the script is exactly one {lit}`SELECT` statement: the only kind of statement that a
two-state observation reads ({name}`Model.Syntax.Statement.asQuery?`). A read of a {lit}`PRAGMA` is a
query ({name}`Script.isQuery`) but not a {lit}`SELECT`. -/
def Script.isSelect (script : Script) : Bool :=
  match script.statements with
  | [(statement, _)] => statement.asQuery?.isSome
  | [] | _ :: _ :: _ => false

/-- The shared part of the query tactics: it tries {lit}`decide`, then {lit}`rfl`, because a script with a
value {lit}`$x` or with an argument holds a free variable, which {lit}`decide` refuses, and
{name}`Script.isQuery` reads only the statements, so {lit}`rfl` proves it. The proof {lit}`id rfl` has the
type of the goal, so that the instances of {lit}`Decidable` below match a proposition that holds it. The
error says what a query is. -/
elab "check_query_shape" : tactic => do
  try evalTactic (← `(tactic| first | decide | exact id rfl))
  catch _ => throwError "the script must be one read-only statement: a SELECT, or PRAGMA foreign_keys without a value; remove the other statements, or use Database.run"

/-- The tactic that proves the argument {lit}`query` of the two-state assertions, such as
{lit}`holdsSince`. It proves what {lit}`check_query_shape` proves, and then refuses a script that is not
a {lit}`SELECT`, because the two-state observation reads no other statement. A schema name in a source is
allowed. -/
elab "check_two_state_query" : tactic => do
  let type ← (← getMainGoal).getType
  evalTactic (← `(tactic| check_query_shape))
  if (queryScript? type).isSome && !(← queryTestHolds ``Script.isSelect type) then
    throwError "a two-state assertion reads one SELECT statement; a PRAGMA is not observed over two databases, so use a one-state assertion"

/-- The tactic that proves the argument {lit}`query` of {lit}`Holds`, {lit}`Empty` and
{lit}`Fails`, and of the one-state assertions {lit}`holds` and {lit}`holdsInContext`. It proves what
{lit}`check_query_shape` proves, and then refuses a query whose source names a schema, as
{lit}`before.t` does: a one-state assertion has no initial database to read it from, and the model
would give no rows. The error names the assertions that take the initial database. -/
elab "check_query" : tactic => do
  let type ← (← getMainGoal).getType
  evalTactic (← `(tactic| check_query_shape))
  if ← queryTestHolds ``Script.namesSchema type then
    throwError "the query has a source that names a schema, such as before.t: a one-state assertion has no initial database to read it from; use holdsSince or holdsInContextSince with the initial database, or the ensuresFrom claim, or remove the schema name"

/-- {lit}`Holds q db`: query {lit}`q` runs on {lit}`db` without error and gives at least one row,
for every result that SQLite may give for it. In terms of the formula: the run of {lit}`q` on
{lit}`db` in the default environment returns a result that is not empty ({name}`Run.returnsResult`):
the run does not stop, and its one output is {name}`Output.rows` with at least one row, or a
nonempty {name}`Output.oneOf` in which each result has at least one row. It does not hold when the
output is {name}`Output.unmodeled`, for example for a query that reads the clock. For example, on a
table {lit}`invoices` with a row of amount 0, {lit}`Holds (sql r"SELECT 1 FROM invoices WHERE amount = 0") db`. -/
abbrev Holds (q : Script) (db : Database) (_query : q.isQuery = true := by check_query) : Prop :=
  (db.run q).returnsResult (· ≠ [])

/-- {lit}`Empty q db`: query {lit}`q` runs on {lit}`db` without error and gives no row, for every
result that SQLite may give for it. In terms of the formula: the run of {lit}`q` on {lit}`db` in the
default environment returns an empty result ({name}`Run.returnsResult`): the run does not stop, and
its one output is {name}`Output.rows` without rows, or a nonempty {name}`Output.oneOf` in which each
result has no row. It does not hold when the output is {name}`Output.unmodeled`. -/
abbrev Empty (q : Script) (db : Database) (_query : q.isQuery = true := by check_query) : Prop :=
  (db.run q).returnsResult (· = [])

/-- {lit}`Fails q db`: query {lit}`q` fails on {lit}`db`: the run of {lit}`q` on {lit}`db` in the
default environment does not stop, and its one output is {name}`Output.error`, with any result code
({name}`Run.returnsError`). It does not hold when the output is {name}`Output.unmodeled`. -/
abbrev Fails (q : Script) (db : Database) (_query : q.isQuery = true := by check_query) : Prop :=
  (db.run q).returnsError fun _ => True

instance (q : Script) (db : Database) (query : q.isQuery = true) : Decidable (Holds q db query) :=
  inferInstanceAs (Decidable ((db.run q).returnsResult (· ≠ [])))

instance (q : Script) (db : Database) (query : q.isQuery = true) : Decidable (Empty q db query) :=
  inferInstanceAs (Decidable ((db.run q).returnsResult (· = [])))

instance (q : Script) (db : Database) (query : q.isQuery = true) : Decidable (Fails q db query) :=
  inferInstanceAs (Decidable ((db.run q).returnsError fun _ => True))

end Belay.Sqlite
