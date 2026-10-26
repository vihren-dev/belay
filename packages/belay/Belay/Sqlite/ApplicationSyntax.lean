import Belay.Sqlite.MigrationPatternSyntax
import Belay.Sqlite.ApplicationClaims
import Belay.Sqlite.ContextObservation

set_option doc.verso true

namespace Belay.Sqlite

open Lean Elab Term

/-- Full-state simulation of a pairing by a migration, optionally restricted to the contexts where
a query guard holds. For example, {lit}`M simulates P where G` states
{name}`Simulation` with the context predicate {name}`Holds.inContext` of the guard. The guard
reads the real context, with its clock, counters and settings. Without a guard, every context is
admitted. Use {lit}`scoped by` when the final contexts may differ. -/
syntax:20 (name := applicationSimulates) term:21 " simulates " term:21 (" scoped " "by " term:21)?
  (" where " term:21)? : term

/-- Elaborate the simulation syntax to the public claims. Without {lit}`scoped by` the result is
{name}`Simulation`, which compares complete final contexts. With it the result is
{name}`ScopedClaim` for the given relation. The guard becomes the context predicate of the claim,
read by {name}`Holds.inContext`; query admission is checked when the term elaborates. -/
@[term_elab applicationSimulates]
def elabApplicationSimulates : TermElab := fun term expectedType => do
  let expanded ← match term with
    | `($migration simulates $pairing scoped by $relation where $guard) =>
      let guarded ← withRef guard `(by check_query)
      `(ScopedClaim (Runnable.toSql $migration) (fun context => Holds.inContext $guard context $guarded)
        $relation $pairing)
    | `($migration simulates $pairing scoped by $relation) =>
      `(ScopedClaim (Runnable.toSql $migration) (fun _ => True) $relation $pairing)
    | `($migration simulates $pairing where $guard) =>
      let guarded ← withRef guard `(by check_query)
      `(Simulation (Runnable.toSql $migration) (fun context => Holds.inContext $guard context $guarded)
        $pairing)
    | `($migration simulates $pairing) =>
      `(Simulation (Runnable.toSql $migration) (fun _ => True) $pairing)
    | _ => throwUnsupportedSyntax
  elabTerm expanded expectedType

end Belay.Sqlite
