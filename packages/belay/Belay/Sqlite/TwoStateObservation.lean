import Belay.Sqlite.Model.TwoStateQuery
import Belay.Sqlite.Run

set_option doc.verso true

/-! The read-only observation of a query over two explicit databases (ADR 0017, S6): the current
database of a connection and a fixed initial database, which the query names with the schema
{lit}`before`. The script comes from the translation of {lit}`sql r"SELECT ... FROM before.t"`, which
keeps the parameter plan and the diagnostics of the surface. The observation resolves and runs the
query with the model's resolver and evaluator ({name}`Belay.Sqlite.Model.observeTwoState`); it
changes no database. -/

namespace Belay.Sqlite

/-- The output of a script of one {lit}`SELECT` statement over the fixed initial database {lit}`initial`
and the database of {lit}`connection`, at the clock value of the optional clock, with the values that
the script binds to its parameters. For example, with the script {lit}`sql r"SELECT a FROM before.t"`,
the rows are those of the table {lit}`t` of {lit}`initial`, whatever {lit}`connection` holds; with
{lit}`sql r"SELECT a FROM t"` they are the rows of the table {lit}`t` of {lit}`connection`.

A script that is not exactly one query, such as a write or an {lit}`ATTACH` statement, is not
observed: the output is {name}`Belay.Sqlite.Model.Output.unmodeled`. A source of the schema
{lit}`before` is observed only here; the run of the same script
({name}`Script.runOn`) refuses it. Use {name}`Script.runOn` for every script that does not name
the schema {lit}`before`. -/
def Script.observeTwoState (script : Script) (initial : Database.Raw) (connection : Connection)
    (clock : Option Belay.Sqlite.Model.Clock := none) : Output :=
  match script.statements with
  | [(statement, parameters)] =>
    match statement.asQuery? with
    | some (query, subqueries) =>
      Belay.Sqlite.Model.observeTwoState runContext clock 0 initial connection parameters query subqueries
    | none => .unmodeled "A two-state observation reads one SELECT statement; remove the other kind of statement"
  | _ => .unmodeled "A two-state observation reads one SELECT statement; give exactly one statement"

/-- For every initial database, connection, clock and script of one statement that is a query such that neither
the query nor a subquery has a source with a schema name, the observation is the output of the ordinary step of
that statement. In plain words: a script with no source that names a schema is observed as it runs, whatever initial database is given, so the
two-state observation extends the ordinary run and a surface program does not gain a connection to
an initial database. Proof sketch: {name}`Belay.Sqlite.Model.observeTwoState_ordinary`. -/
theorem Script.observeTwoState_ordinary (initial : Database.Raw) (connection : Connection)
    (clock : Option Belay.Sqlite.Model.Clock) (statement : Belay.Sqlite.Model.Syntax.Statement)
    (parameters : List Belay.Sqlite.Model.Value) (query : Belay.Sqlite.Model.Syntax.Subquery)
    (subqueries : List Belay.Sqlite.Model.Syntax.Subquery)
    (found : statement.asQuery? = some (query, subqueries))
    (plain : Belay.Sqlite.Model.usesSchema query subqueries = false) :
    (Script.mk [(statement, parameters)]).observeTwoState initial connection clock =
      (Belay.Sqlite.Model.runScriptStep runContext clock 0 connection statement parameters).output := by
  simp only [Script.observeTwoState, found]
  exact Belay.Sqlite.Model.observeTwoState_ordinary runContext clock 0 initial connection parameters statement
    query subqueries found plain

/-- For every script that is not exactly one statement, the observation is not modeled. In plain
words: an empty script or a script of several statements, such as a write followed by a query, is
refused, and never gives rows. -/
theorem Script.observeTwoState_single (script : Script) (initial : Database.Raw) (connection : Connection)
    (clock : Option Belay.Sqlite.Model.Clock) (notOne : ∀ item, script.statements ≠ [item]) :
    ∃ reason, script.observeTwoState initial connection clock = .unmodeled reason := by
  unfold Script.observeTwoState
  split
  · rename_i statement parameters same
    exact absurd same (notOne _)
  · exact ⟨_, rfl⟩

end Belay.Sqlite
