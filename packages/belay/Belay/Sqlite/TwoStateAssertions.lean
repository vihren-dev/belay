import Belay.Sqlite.AssertionTerms
import Belay.Sqlite.TwoStateObservation
import Belay.Sqlite.QuerySuccess

set_option doc.verso true

/-!
Two-state query assertions (ADR 0017, S6). A query that names the schema {lit}`before`, as in
{lit}`sql r"SELECT a FROM before.t"`, reads the initial database of a run. The one-state assertions
({lit}`Holds`, {lit}`holds`, {lit}`holdsInContext`) refuse such a query, because they have no initial
database. The two-state assertions here take the initial database as an argument, so a claim can
compare the reached database with its start. They share the evaluator of the model with the
one-state assertions ({name}`Belay.Sqlite.Model.observeTwoState`); no string replacement implements
{lit}`before`.

* {lit}`Holds.inContextSince` observes the query with the clock, next statement index and
  connection of a context, as {lit}`Holds.inContext` does.
* {lit}`Holds.reachedSince` observes the query with the default observation of the database that a
  context sees, as {lit}`Holds.reached` does.
* {lit}`holdsSince` and {lit}`holdsInContextSince` are the matching assertions on contexts.
* {lit}`FreshEnsuresFrom` is the fresh-run claim whose postcondition may name the captured start.
-/

namespace Belay.Sqlite
open Std.Do Model

/-- The output of a script of one query statement over the fixed initial database {lit}`initial` and the
connection of a context, at the clock and the statement index of the context. A script that is not
exactly one query is {name}`Output.unmodeled`. The observation runs nothing: it changes no database.
With index zero and the clock {lit}`none` it is {name}`Script.observeTwoState`. -/
def Script.observeTwoStateIn (script : Script) (initial : Database.Raw) (context : ExecutionContext) : Output :=
  match script.statements with
  | [(statement, parameters)] =>
    match statement.asQuery? with
    | some (query, subqueries) =>
      Model.observeTwoState runContext context.clock context.index initial context.connection parameters query subqueries
    | none => .unmodeled "A two-state observation reads one SELECT statement; remove the other kind of statement"
  | _ => .unmodeled "A two-state observation reads one SELECT statement; give exactly one statement"

/-- For every script, initial database, connection and clock, {name}`Script.observeTwoState` is the
observation in the context of that clock, index zero and that connection. Proof sketch: both
definitions match the script in the same way and pass index zero. -/
theorem Script.observeTwoState_eq_in (script : Script) (initial : Database.Raw) (connection : Connection)
    (clock : Option Clock) :
    script.observeTwoState initial connection clock = script.observeTwoStateIn initial ⟨clock, 0, connection, []⟩ := by
  unfold Script.observeTwoState Script.observeTwoStateIn
  rfl

/-- The real-context two-state assertion: the single query gives at least one row, for every result that
SQLite may give for it, when it runs from the context over the initial database {lit}`initial`. A source
{lit}`before.t` reads the table {lit}`t` of {lit}`initial`; every other source reads the database of the
context's connection, with the actual clock at the context's next statement index, the counters, the
settings and the open transaction. It does not hold when the output is empty, an error or unmodeled.
The initial database is a plain argument, so the claim can use any database as the start. -/
def Holds.inContextSince (script : Script) (initial : Database) (context : ExecutionContext)
    (_query : script.isQuery = true := by check_two_state_query) : Prop :=
  (script.observeTwoStateIn initial.raw context).hasRows = true

instance (script : Script) (initial : Database) (context : ExecutionContext) (query : script.isQuery = true) :
    Decidable (Holds.inContextSince script initial context query) :=
  inferInstanceAs (Decidable (_ = true))

/-- The default two-state assertion at a context: the query gives rows over the initial database
{lit}`initial` and the database that the context's connection sees, observed with the default
observation of that database ({name}`ExecutionContext.defaultObservation`): no clock, unknown counters,
foreign keys off and no open transaction. The default observation inputs are documented in
{name}`Holds.reached`. -/
def Holds.reachedSince (script : Script) (initial : Database) (context : ExecutionContext)
    (query : script.isQuery = true := by check_two_state_query) : Prop :=
  Holds.inContextSince script initial context.defaultObservation query

instance (script : Script) (initial : Database) (context : ExecutionContext) (query : script.isQuery = true) :
    Decidable (Holds.reachedSince script initial context query) :=
  inferInstanceAs (Decidable (Holds.inContextSince script initial context.defaultObservation query))

/-- {lit}`holdsSince start q`: the query {lit}`q` gives rows over the initial database {lit}`start` and the
database that the context sees, with the default observation ({name}`Holds.reachedSince`). The query
may name the schema {lit}`before`. It holds in an ordinary triple at every context; to name the start of a
fresh run use {lit}`FreshEnsuresFrom`. -/
def holdsSince (start : Database) (script : Script)
    (query : script.isQuery = true := by check_two_state_query) : ContextAssertion :=
  fun context => ⌜Holds.reachedSince script start context query⌝

/-- {lit}`holdsInContextSince start q`: the query {lit}`q` gives rows over the initial database
{lit}`start` when it runs from the context ({name}`Holds.inContextSince`), with the actual clock,
counters, settings and open transaction. -/
def holdsInContextSince (start : Database) (script : Script)
    (query : script.isQuery = true := by check_two_state_query) : ContextAssertion :=
  fun context => ⌜Holds.inContextSince script start context query⌝

/-- For every query that is a {lit}`SELECT` and names no schema, every initial database and every context,
the two-state assertion in the context is the one-state assertion {name}`Holds.inContext`. In plain words:
without a {lit}`before` source the initial database is not read, so a two-state assertion extends the
one-state one. Proof sketch: the query has one statement; {name}`Script.observeTwoState_ordinary` and the
definition of the run from a context give the same output. -/
theorem Holds.inContextSince_iff_inContext (script : Script) (initial : Database) (context : ExecutionContext)
    (query : script.isQuery = true) (select : script.isSelect = true) (plain : script.namesSchema = false) :
    Holds.inContextSince script initial context query ↔ Holds.inContext script context query := by
  obtain ⟨statement, values, one⟩ := Script.singleton_of_isQuery query
  unfold Holds.inContextSince Holds.inContext Script.observeTwoStateIn Script.outputIn
  rw [one]
  cases found : statement.asQuery? with
  | none => simp [Script.isSelect, one, found] at select
  | some pair =>
    obtain ⟨q, subs⟩ := pair
    simp only [Script.namesSchema, one, found] at plain
    simp only [found]
    rw [observeTwoState_ordinary runContext context.clock context.index initial.raw context.connection values statement q subs found plain]
    cases step : runScriptStep runContext context.clock context.index context.connection statement values <;>
      simp [runScriptFrom, step, RunStep.output]

/-- For every query that is a {lit}`SELECT` and names no schema, every initial database and every
context, the default two-state assertion is the one-state assertion {name}`Holds.reached`. A read of a
{lit}`PRAGMA` is not covered: the two-state observation does not model it. Proof sketch:
{name}`Holds.inContextSince_iff_inContext` at the default observation. -/
theorem Holds.reachedSince_iff_reached (script : Script) (initial : Database) (context : ExecutionContext)
    (query : script.isQuery = true) (select : script.isSelect = true) (plain : script.namesSchema = false) :
    Holds.reachedSince script initial context query ↔ Holds.reached script context query :=
  Holds.inContextSince_iff_inContext script initial _ query select plain

/-- The fresh-run claim whose postcondition may name the captured start: for each admitted database
satisfying the precondition and each complete environment, every branch from the initial context returns
a value and a reached context that satisfy the postcondition {lit}`post start`. The start is the
database of the initial context. It is the claim {name}`FreshEnsures` when the postcondition ignores the
start ({lit}`FreshEnsuresFrom.iff_ensures`). -/
def FreshEnsuresFrom {α : Type} (program : Sql α) (pre : Database → Prop)
    (post : Database → PostCond α (.arg ExecutionContext .pure)) : Prop :=
  FreshTriple program pre fun start _ value final => ((post start).1 value final).down

/-- For every program, precondition and postcondition, the claim that ignores the start is the fresh-run
claim {name}`FreshEnsures`. Proof sketch: both unfold to the same fresh triple. -/
theorem FreshEnsuresFrom.iff_ensures {α : Type} (program : Sql α) (pre : Database → Prop)
    (post : PostCond α (.arg ExecutionContext .pure)) :
    FreshEnsuresFrom program pre (fun _ => post) ↔ FreshEnsures program pre post := Iff.rfl

end Belay.Sqlite
