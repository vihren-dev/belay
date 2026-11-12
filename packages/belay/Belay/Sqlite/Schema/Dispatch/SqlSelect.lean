import Belay.Sqlite.Queries.Automation.SqlSelectLeaf
import Belay.Sqlite.Queries.Automation.SqlSelectRules
import Belay.Sqlite.Schema.Rows.SqlSelectRules
import Lean.Meta.Tactic.Subst

set_option doc.verso true

namespace Belay.Sqlite.Select
open Lean Meta Elab Tactic

/-- The phases whose rules apply to a hypothesis of the given type: membership in the results of a
query, membership in the scanned rows of a table, or any other fact. -/
def phasesOfFact (type : Expr) : List SelectPhase :=
  match type.getAppFnArgs with
  | (``Membership.mem, #[_, _, _, collection, _]) =>
    match collection.getAppFn.constName? with
    | some ``Belay.Sqlite.Model.Resolved.Query.possibleResults =>
      [.window, .order, .distinct, .project, .having, .aggregate, .group, .compound, .subquery]
    | some ``Belay.Sqlite.Database.scanAt => [.source]
    | _ => [.filter, .expression]
  | _ => [.filter, .expression]

/-- Whether a term reads the query model: a declaration of the resolved query
({lit}`Belay.Sqlite.Model.Resolved`), such as {lit}`Resolved.Query.results`, a phase function such as
{lit}`Resolved.filtered`, or the scanned rows of a table ({lit}`Database.scanAt`). -/
def readsQueryModel (term : Expr) : Bool :=
  (term.find? fun part => match part.constName? with
    | some name => (`Belay.Sqlite.Model.Resolved).isPrefixOf name || name == ``Belay.Sqlite.Database.scanAt
    | none => false).isSome

/-- Whether the goal is about a query: its target or one of its hypotheses reads the query model
({name}`readsQueryModel`). -/
def aboutQuery (goal : MVarId) : MetaM Bool := goal.withContext do
  if readsQueryModel (← instantiateMVars (← goal.getType)) then return true
  (← getLCtx).anyM fun declaration => do
    if declaration.isImplementationDetail then return false
    return readsQueryModel (← instantiateMVars declaration.type)

end Belay.Sqlite.Select
