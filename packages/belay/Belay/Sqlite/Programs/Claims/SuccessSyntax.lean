import Belay.Sqlite.Programs.Scripts.Success
import Belay.Sqlite.Programs.Claims.Queries

set_option doc.verso true

namespace Belay.Sqlite

open Lean Elab Term

/-- Success of a program, with an optional schema and an optional SQL guard.

- {lit}`program succeeds` means {name}`Succeeds` on every database: the predicate is always true.
- {lit}`program succeeds on shop` covers every database with the catalog of the database {lit}`shop`
  ({name}`Database.HasCatalog`), for example {lit}`makeStrict succeeds on shop`.
- {lit}`program succeeds where query` covers every database on which the SQL guard holds
  ({name}`Holds`). The guard must be exactly one read-only statement.
- {lit}`program succeeds on shop where query` needs both the catalog and the guard.

Use the form without {lit}`on` when the claim must hold whatever the schema is. For any other
premise, write {name}`Succeeds` with a predicate. -/
syntax:20 (name := succeedsTerm) term:21 " succeeds" (" on " term:21)? (" where " term:21)? : term

/-- Elaborate success through {name}`Succeeds`, {name}`Database.HasCatalog` and {name}`Holds`.
Generated query checks use the guard's source position so an invalid guard points to its text. -/
@[term_elab succeedsTerm]
def elabSucceeds : TermElab := fun term expectedType => do
  match term with
  | `($program succeeds on $schema where $query) => withRef query do
    elabTerm (← `(Succeeds $program (fun db => Database.HasCatalog db $schema ∧ Holds $query db))) expectedType
  | `($program succeeds on $schema) =>
    elabTerm (← `(Succeeds $program (fun db => Database.HasCatalog db $schema))) expectedType
  | `($program succeeds where $query) => withRef query do
    elabTerm (← `(Succeeds $program (fun db => Holds $query db))) expectedType
  | `($program succeeds) => elabTerm (← `(Succeeds $program (fun _ => True))) expectedType
  | _ => throwUnsupportedSyntax

end Belay.Sqlite
