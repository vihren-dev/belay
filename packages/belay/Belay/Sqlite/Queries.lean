import Belay.Sqlite.Model.QueryOutputs
import Belay.Sqlite.Model.ResolveStatementSingle
import Belay.Sqlite.Model.TwoStateQuery
import Lean.Elab.Tactic.Basic
import Belay.Sqlite.Run

set_option doc.verso true

/-! Queries as propositions over one database (ADR 0017, S2): {lit}`Holds q db`, {lit}`Empty q db`
and {lit}`Fails q db` state what the query {lit}`q` gives on {lit}`db`, for every result that
SQLite may give for it. Each one is decidable, so {lit}`decide` proves it, or its negation, for
a concrete database and query. The query is a script of one read-only statement: the argument
{lit}`query` checks it when the term elaborates, also for a query with parameters. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model Lean Elab Tactic

/-- Whether the script is a query: exactly one statement, which only reads
({name}`Model.Syntax.Statement.readsOnly`). -/
def Script.isQuery (script : Script) : Bool :=
  match script.statements with
  | [(statement, _)] => statement.readsOnly
  | [] | _ :: _ :: _ => false

/-- For every script that is a query, no statement of the script is written as INSERT from a query. Proof sketch:
a query has one statement that only reads, and INSERT from a query writes. -/
theorem Script.noInsertSelect_of_isQuery {script : Script} (query : script.isQuery = true) :
    ∀ entry ∈ script.statements, entry.1.isInsertSelect = false := by
  unfold Script.isQuery at query
  split at query
  · rename_i statement values same
    intro entry member
    rw [same] at member
    obtain rfl := List.mem_singleton.1 member
    cases statement <;> simp_all [Syntax.Statement.readsOnly, Syntax.Statement.isInsertSelect]
  all_goals simp at query

/-- The output of the first statement of the script on the database, with foreign keys off, as
on a new connection: {lean}`(none : Option Output)` for a script without statements. -/
def Script.outputOn (script : Script) (db : Database) : Option Output :=
  (db.raw.run script).outputs.head?

/-- Whether the script is one statement that is a query with a source that names a schema, as
{lit}`SELECT a FROM before.t` does. Such a query needs the initial database of a two-state
observation ({name}`Model.usesSchema`). Every other script, also one that is not a query, gives false. -/
def Script.namesSchema (script : Script) : Bool :=
  match script.statements with
  | [(statement, _)] =>
    match statement.asQuery? with
    | some (query, subqueries) => usesSchema query subqueries
    | none => false
  | [] | _ :: _ :: _ => false

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

/-- The script of the goal {lit}`Script.isQuery script = true`, when the goal has that form. -/
def queryScript? (goal : Expr) : Option Expr :=
  goal.eq?.bind fun (_, isQuery, _) => isQuery.app1? ``Script.isQuery

/-- Whether the Boolean test of the script, such as {name}`Script.namesSchema`, is true for the script of
the goal, by evaluation. A goal that is not a query goal gives false. -/
def queryTestHolds (test : Name) (goal : Expr) : Meta.MetaM Bool := do
  match queryScript? goal with
  | some script => return (← Meta.whnf (mkApp (mkConst test) script)).isConstOf ``Bool.true
  | none => return false

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
for every result that SQLite may give for it. In terms of the formula: the output of
{lit}`q` on {lit}`db` ({name}`Script.outputOn`) is {name}`Output.rows` with at least one row, or
{name}`Output.oneOf` in which each result has at least one row. It does not hold when the
output is {name}`Output.unmodeled`, for example for a query that reads the clock. For example,
on a table {lit}`invoices` with a row of amount 0, {lit}`Holds (sql r"SELECT 1 FROM invoices WHERE amount = 0") db`. -/
def Holds (q : Script) (db : Database) (_query : q.isQuery = true := by check_query) : Prop :=
  (q.outputOn db).any Output.hasRows = true

/-- {lit}`Empty q db`: query {lit}`q` runs on {lit}`db` without error and gives no row, for every
result that SQLite may give for it. In terms of the formula: the output of {lit}`q` on
{lit}`db` is {name}`Output.rows` without rows, or {name}`Output.oneOf` in which each result has no
row. It does not hold when the output is {name}`Output.unmodeled`. -/
def Empty (q : Script) (db : Database) (_query : q.isQuery = true := by check_query) : Prop :=
  (q.outputOn db).any Output.hasNoRows = true

/-- {lit}`Fails q db`: query {lit}`q` fails on {lit}`db`: its output is {name}`Output.error`, with any
result code. It does not hold when the output is {name}`Output.unmodeled`. -/
def Fails (q : Script) (db : Database) (_query : q.isQuery = true := by check_query) : Prop :=
  (q.outputOn db).any Output.isError = true

instance (q : Script) (db : Database) (query : q.isQuery = true) : Decidable (Holds q db query) :=
  inferInstanceAs (Decidable (_ = true))

instance (q : Script) (db : Database) (query : q.isQuery = true) : Decidable (Empty q db query) :=
  inferInstanceAs (Decidable (_ = true))

instance (q : Script) (db : Database) (query : q.isQuery = true) : Decidable (Fails q db query) :=
  inferInstanceAs (Decidable (_ = true))

end Belay.Sqlite
