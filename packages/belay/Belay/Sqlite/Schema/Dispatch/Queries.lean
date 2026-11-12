import Belay.Sqlite.Model.Queries.Preparation.QueryOutputs
import Belay.Sqlite.Model.Schema.Triggers.ResolveStatementSingle
import Belay.Sqlite.Model.Queries.Preparation.TwoStateQuery
import Belay.Sqlite.Model.Schema.Dispatch.TwoStateQuery
import Lean.Elab.Tactic.Basic
import Belay.Sqlite.Schema.Dispatch.Run

set_option doc.verso true

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

/-- The script of the goal {lit}`Script.isQuery script = true`, when the goal has that form. -/
def queryScript? (goal : Expr) : Option Expr :=
  goal.eq?.bind fun (_, isQuery, _) => isQuery.app1? ``Script.isQuery

/-- Whether the Boolean test of the script, such as {name}`Script.namesSchema`, is true for the script of
the goal, by evaluation. A goal that is not a query goal gives false. -/
def queryTestHolds (test : Name) (goal : Expr) : Meta.MetaM Bool := do
  match queryScript? goal with
  | some script => return (← Meta.whnf (mkApp (mkConst test) script)).isConstOf ``Bool.true
  | none => return false

end Belay.Sqlite
