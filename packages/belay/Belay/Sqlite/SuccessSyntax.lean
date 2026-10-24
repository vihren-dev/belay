import Belay.Sqlite.Success
import Belay.Sqlite.Queries

set_option doc.verso true

namespace Belay.Sqlite

open Lean Elab Term

/-- {lit}`program succeeds where query` means {name}`Succeeds` under the predicate
{name}`Holds` for that query. The query must be exactly one read-only statement. -/
syntax:20 (name := succeedsWhereTerm) term:21 " succeeds" " where " term:21 : term

/-- {lit}`program succeeds` means {name}`Succeeds` under the predicate that is always true. -/
syntax:20 (name := succeedsTerm) term:21 " succeeds" : term

/-- Elaborate conditional success through {name}`Succeeds` and {name}`Holds`. Generated
query checks use the query's source position so an invalid precondition points to its text. -/
@[term_elab succeedsWhereTerm]
def elabSucceedsWhere : TermElab := fun term expectedType => do
  match term with
  | `($program succeeds where $query) => withRef query do
    elabTerm (← `(Succeeds $program (fun db => Holds $query db))) expectedType
  | _ => throwUnsupportedSyntax

/-- Elaborate unconditional success through {name}`Succeeds` with the always-true predicate. -/
@[term_elab succeedsTerm]
def elabSucceeds : TermElab := fun term expectedType => do
  match term with
  | `($program succeeds) => elabTerm (← `(Succeeds $program (fun _ => True))) expectedType
  | _ => throwUnsupportedSyntax

end Belay.Sqlite
