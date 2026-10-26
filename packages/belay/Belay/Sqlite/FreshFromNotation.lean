import Belay.Sqlite.FreshNotation
import Belay.Sqlite.TwoStateAssertions

set_option doc.verso true

/-!
The {lit}`program ensuresFrom start => post` notation for fresh-run claims that compare the reached
database with the captured start (ADR 0017, S6). It elaborates to {lit}`FreshEnsuresFrom` and adds no
semantics. The name {lit}`start` is the database that the run starts from, for the postcondition
{lit}`post`, in which a query may name the schema {lit}`before` through {lit}`holdsSince`.
-/

namespace Belay.Sqlite

open Lean Elab Term

/-- {lit}`program ensuresFrom start => post` is the fresh-run claim {name}`FreshEnsuresFrom` for every
admitted database {lit}`start`. The postcondition {lit}`post` may use {lit}`start`, for example
{lit}`ifOk (holdsSince start (sql r"SELECT 1 FROM before.t"))`. -/
syntax:20 (name := freshEnsuresFromTerm) term:21 " ensuresFrom " ident " => " term:21 : term

/-- {lit}`program ensuresFrom start => post where query` restricts the claim to the databases on which
the one-state query {name}`Holds` with its default observation. The guard cannot name {lit}`before`, which
the check of its query refuses. -/
syntax:20 (name := freshEnsuresFromWhereTerm) term:21 " ensuresFrom " ident " => " term:21 " where " term:21 : term

/-- Elaborate both forms to {name}`FreshEnsuresFrom`, with the always-true predicate or {name}`Holds` as
the database predicate. The generated query check uses the source position of the guard. -/
@[term_elab freshEnsuresFromTerm, term_elab freshEnsuresFromWhereTerm]
def elabFreshEnsuresFrom : TermElab := fun term expectedType => do
  match term with
  | `($program ensuresFrom $start => $post where $guard) =>
    let guarded ← withRef guard `(by check_query)
    elabTerm (← `(FreshEnsuresFrom (Runnable.toSql $program) (fun db => Holds $guard db $guarded)
      (fun $start => $post))) expectedType
  | `($program ensuresFrom $start => $post) =>
    elabTerm (← `(FreshEnsuresFrom (Runnable.toSql $program) (fun _ => True) (fun $start => $post))) expectedType
  | _ => throwUnsupportedSyntax

end Belay.Sqlite
