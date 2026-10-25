import Belay.Sqlite.MigrationPatternFresh

set_option doc.verso true

namespace Belay.Sqlite

open Lean Elab Term

/-- Mark all successful outputs of this exact script or program as hidden in a
view. Errors, stops and returned values remain. For example, {lean}`quiet (Sql.pure ())`
is a descriptor, not an action in a {name}`Sql` do block. Use {name}`Sql.View.bind`
to mark a segment explicitly, or {name}`Sql.View.identity` to retain all outputs. -/
def quiet {σ α : Type} [Runnable σ α] (program : σ) : Sql.View (Runnable.toSql program) :=
  Sql.View.quiet (Runnable.toSql program)

/-- Fresh query preservation, with an optional SQL guard interpreted by default
{name}`Holds`. Read-only query admission is checked when the term elaborates. -/
syntax:20 (name := migrationPreserves) term:21 " preserves " term:21 (" where " term:21)? : term

/-- Fresh query translation, retaining both queries' return values and observations.
The optional SQL guard uses default {name}`Holds`; both queries must be read-only. -/
syntax:20 (name := migrationTranslates) term:21 " translates " term:21 " to " term:21
  (" where " term:21)? : term

/-- Fresh full-context commutation, optionally with a replacement application and a
default-{name}`Holds` SQL guard. Both applications return the same Lean type. -/
syntax:20 (name := migrationCommutes) term:21 " commutes " "with " term:21
  (" as " term:21)? (" where " term:21)? : term

/-- Elaborate the named patterns to their public fresh-context primitives. Each
quantifies over all admitted bundled databases and complete environments, then tests
migration success at the original context. Query guards retain the default observation;
use the explicit context predicates in {name}`Migration.TranslatesOn` or
{name}`Migration.CommutesAsOn` for other restrictions. -/
@[term_elab migrationPreserves, term_elab migrationTranslates, term_elab migrationCommutes]
def elabMigrationPattern : TermElab := fun term expectedType => do
  let expanded ← match term with
    | `($migration preserves $query where $guard) =>
      let admitted ← withRef query `(by check_query)
      let guarded ← withRef guard `(by check_query)
      `(Migration.QueryPreserves (Runnable.toSql $migration) $query (fun db => Holds $guard db $guarded) $admitted)
    | `($migration preserves $query) =>
      let admitted ← withRef query `(by check_query)
      `(Migration.QueryPreserves (Runnable.toSql $migration) $query (fun _ => True) $admitted)
    | `($migration translates $query to $replacement where $guard) =>
      let original ← withRef query `(by check_query)
      let changed ← withRef replacement `(by check_query)
      let guarded ← withRef guard `(by check_query)
      `(Migration.QueryTranslates (Runnable.toSql $migration) $query $replacement
        (fun db => Holds $guard db $guarded) $original $changed)
    | `($migration translates $query to $replacement) =>
      let original ← withRef query `(by check_query)
      let changed ← withRef replacement `(by check_query)
      `(Migration.QueryTranslates (Runnable.toSql $migration) $query $replacement (fun _ => True) $original $changed)
    | `($application commutes with $migration as $replacement where $guard) =>
      let guarded ← withRef guard `(by check_query)
      `(Migration.CommutesAs (Runnable.toSql $migration) (Runnable.toSql $application)
        (Runnable.toSql $replacement) (fun db => Holds $guard db $guarded))
    | `($application commutes with $migration as $replacement) =>
      `(Migration.CommutesAs (Runnable.toSql $migration) (Runnable.toSql $application)
        (Runnable.toSql $replacement) (fun _ => True))
    | `($application commutes with $migration where $guard) =>
      let guarded ← withRef guard `(by check_query)
      `(Migration.Commutes (Runnable.toSql $migration) (Runnable.toSql $application) (fun db => Holds $guard db $guarded))
    | `($application commutes with $migration) =>
      `(Migration.Commutes (Runnable.toSql $migration) (Runnable.toSql $application) (fun _ => True))
    | _ => throwUnsupportedSyntax
  elabTerm expanded expectedType

end Belay.Sqlite
