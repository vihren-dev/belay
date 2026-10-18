import Belay.Sqlite.Resolution.Resolved

set_option doc.verso true

/-! The catalog that a resolved statement leaves when it succeeds. Resolution and
execution change the catalog with the same functions ({lit}`Catalog.createTable`,
{lit}`Catalog.createIndex`, {lit}`Catalog.addColumn`), and this function names that
change once, so the theorems that relate them can state it. -/

namespace Belay.Sqlite.Resolved

/-- The catalog after the statement succeeds on the given catalog: CREATE TABLE, CREATE
INDEX and ADD COLUMN apply their catalog function, and every other statement leaves the catalog unchanged. Transaction control is not a
catalog change here; {lit}`ResolveState.after` handles it. For example,
{lean}`(Statement.begin.applyCatalog [] : Catalog)` is the empty catalog. -/
def Statement.applyCatalog : Statement → Catalog → Catalog
  | .createTable _ name table, catalog => catalog.createTable name table
  | .createIndex _ name index, catalog => catalog.createIndex name index
  | .addColumn position column, catalog => catalog.addColumn position column
  | .begin, catalog | .commit, catalog | .rollback, catalog | .insert .., catalog | .update .., catalog
  | .upsert .., catalog | .delete .., catalog | .prepareError _, catalog | .query _, catalog => catalog

/-- Whether the statement is transaction control: BEGIN, COMMIT or ROLLBACK. These change the saved catalog of a transaction instead of the
catalog; every other statement is not control. -/
def Statement.isControl : Statement → Bool
  | .begin | .commit | .rollback => true
  | .createTable .. | .createIndex .. | .addColumn .. | .insert .. | .update .. | .upsert .. | .delete ..
  | .prepareError _ | .query _ => false

end Belay.Sqlite.Resolved
