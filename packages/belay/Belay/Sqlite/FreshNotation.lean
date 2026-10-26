import Belay.Sqlite.AssertionTerms
import Belay.Sqlite.Queries

set_option doc.verso true

/-!
The {lit}`program ensures post` notation for fresh-run claims. It elaborates to
{lit}`FreshEnsures` over the program and checks the optional {lit}`where` query at its own source
position. It adds no semantics: the claim is the public primitive.
-/

namespace Belay.Sqlite

open Lean Elab Term

/-- {lit}`program ensures post` is the fresh-run claim {name}`FreshEnsures` for every admitted
database. The program is a {name}`Sql` program or a script. The postcondition is a standard
Std.Do postcondition, for example {lit}`ifOk (holds (sql r"SELECT 1"))`,
{lit}`andOk ⌜True⌝` or {lit}`⇓ value => ...`. -/
syntax:20 (name := freshEnsuresTerm) term:21 " ensures " term:21 : term

/-- {lit}`program ensures post where query` restricts the fresh-run claim to the databases on
which the query {name}`Holds` with its default observation. The query must be exactly one
read-only statement, which the term checks at the query's source. -/
syntax:20 (name := freshEnsuresWhereTerm) term:21 " ensures " term:21 " where " term:21 : term

/-- Elaborate both forms to {name}`FreshEnsures`, with the always-true predicate or
{name}`Holds` as the database predicate. The generated query check uses the query's source
position, so an invalid query points to its text. -/
@[term_elab freshEnsuresTerm, term_elab freshEnsuresWhereTerm]
def elabFreshEnsures : TermElab := fun term expectedType => do
  match term with
  | `($program ensures $post where $guard) =>
    let guarded ← withRef guard `(by check_query)
    elabTerm (← `(FreshEnsures (Runnable.toSql $program) (fun db => Holds $guard db $guarded) $post)) expectedType
  | `($program ensures $post) =>
    elabTerm (← `(FreshEnsures (Runnable.toSql $program) (fun _ => True) $post)) expectedType
  | _ => throwUnsupportedSyntax

end Belay.Sqlite
