import RebuildKeepsInvariant

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-! The copy step of the guide's table rebuild (ADR 0017, S6, part 3). The INSERT from a query of
{lit}`makeStrict` copies the three columns of the customers into the new customers table. This module names the
resolved statement and the facts about the catalog that the success of the copy needs: the shapes of the old and
the new table, and the keys that the new table checks. The facts are checked by evaluation on the catalog that the
model reaches after the first three statements, and they hold for the catalog of every connection that has the
same resolution state. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace RebuildGuide

/-- The name of the table of the customers. -/
def customersName : Identifier := name! "customers"

/-- The query of the copy: the three columns of the table at position 0, the old customers, in order. -/
def copyQuery : Resolved.Query :=
  Resolved.Query.simple [Resolved.QuerySource.first 0] none ((List.range 3).map fun position => .scalar (.column position))
    ["id", "name", "email"]

/-- The resolved copy: the table at position 2, the new customers, takes the three cells of the query in order. -/
def copyStatement : Resolved.Statement :=
  .insertSelect 2 ((List.range 3).map .source) copyQuery [] [] none [] none

/-- The fourth statement of the rebuild resolves to {name}`copyStatement` on the resolution state that the model
reaches before it. Proof sketch: evaluation. -/
theorem copy_resolves : ∃ after, resolveStatement runContext (reachedAfter 3).resolveState makeStrict.statements[3].1 =
    .ok (copyStatement, after) := ⟨_, by with_unfolding_all rfl⟩

/-- The key of the primary key of {lit}`id`, which is the rowid alias of both tables. -/
def aliasKey : UniqueKey := { terms := [{ term := .column 0 }], filter := none }

/-- Whether a table definition is that of the old customers: {lit}`id` is the rowid alias, the table has a rowid, and
the columns are {lit}`id INTEGER`, {lit}`name TEXT` and {lit}`email TEXT NOT NULL`. -/
def oldFacts (shape : CatalogTable) : Bool :=
  shape.rowidAlias == some 0 && !shape.withoutRowid && shape.columns.map CatalogColumn.notNull == [false, false, true] &&
    shape.columns.map CatalogColumn.affinity == [.integer, .text, .text]

/-- The definition of the new customers, as the model builds it for the CREATE TABLE of the rebuild: the table at
position 2 of the catalog that the model reaches after the first three statements. The premise of the success claim
asks that every old customer fits its STRICT types ({name}`LiteralData.typesFit`). The table without columns is not
reached; it only completes the lookup. -/
def strictShape : CatalogTable := ((reachedAfter 3).resolveState.catalog.tableAt 2).getD { columns := [] }

/-- Whether a table definition is that of the new customers: {lit}`id` is the rowid alias with an integer type, no
column is generated, the table has no CHECK, the STRICT types are {lit}`INTEGER`, {lit}`TEXT` and {lit}`TEXT`, and
the columns have the NOT NULL and the affinities of the old table. -/
def newFacts (shape : CatalogTable) : Bool :=
  shape.rowidAlias == some 0 && LiteralData.aliasReady shape &&
    shape.columns.all (fun column => column.generated.isNone) && shape.allChecks.isEmpty &&
    shape.columns.map CatalogColumn.strictType == [some .integer, some .text, some .text] &&
    shape.columns.map CatalogColumn.notNull == [false, false, true] &&
    shape.columns.map CatalogColumn.affinity == [.integer, .text, .text]

/-- The definition of the new customers has the facts of {name}`newFacts`. Proof sketch: kernel evaluation. -/
theorem strictShape_facts : newFacts strictShape = true := by decide +kernel

/-- Whether a catalog has the old customers at position 0, read through the primary key only, and the new customers
at position 2 with their definition {name}`strictShape`, with the primary key as its only key. -/
def catalogFacts (catalog : Catalog) : Bool :=
  (match catalog.findTable customersName with
    | some (position, shape) =>
      position == 0 && oldFacts shape && catalog.accessKeys 0 shape == [([{ term := .column 0 }], none)]
    | none => false) &&
  catalog.tableAt 2 == some strictShape && catalog.uniqueKeys 2 strictShape == [aliasKey]

/-- The catalog that the model reaches after the first three statements has the facts. Proof sketch: kernel
evaluation. -/
theorem catalogFacts_reached : catalogFacts (reachedAfter 3).resolveState.catalog = true := by decide +kernel

/-- For every catalog that has the facts and finds the customers at position 0 with the definition {lit}`oldShape`:
the definition is that of the old customers, the primary key is its only access key, and the new customers are at
position 2, with the definition {name}`strictShape` and the primary key as their only unique key. Proof sketch:
unfold {name}`catalogFacts` and read the match. -/
theorem catalogFacts_unpack {catalog : Catalog} (facts : catalogFacts catalog = true) {oldShape : CatalogTable}
    (found : catalog.findTable customersName = some (0, oldShape)) :
    oldFacts oldShape = true ∧ catalog.accessKeys 0 oldShape = [([{ term := .column 0 }], none)] ∧
      catalog.tableAt 2 = some strictShape ∧ catalog.uniqueKeys 2 strictShape = [aliasKey] := by
  unfold catalogFacts at facts
  rw [found] at facts
  simp only [Bool.and_eq_true, beq_iff_eq] at facts
  exact ⟨facts.1.1.1.2, facts.1.1.2, facts.1.2, facts.2⟩

end RebuildGuide
