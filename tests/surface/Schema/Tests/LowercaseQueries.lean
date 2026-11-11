import LowercaseExpansion

set_option doc.verso true

/-! The guide's lookups across the lowercase-field expansion (ADR 0017, S6). The general theorems
{lit}`DerivedColumnMigration.queryTranslates` and {lit}`DerivedColumnMigration.queryPreserves` take a
description of the move of a read for every site. This module gives that description for the lookups
{lit}`WHERE lower(source) = lower(?n)` and {lit}`WHERE stored = lower(?n)`, from the filter laws of
{lit}`LowercaseFilters` and the resolution laws of {lit}`LowercaseLookups`, and derives the guide's two
claims for every database that has a site. -/

namespace LowercaseFixture
open Belay.Sqlite Belay.Sqlite.Model Belay.Sqlite.Model.Resolved

/-- The lookup {lit}`SELECT id FROM t WHERE lower(source) = lower(?n)` as a query script with the value
bound to its parameter. -/
def originalLookupScript (tableName : Identifier) (alias : Option Identifier) (idName sourceName : Identifier)
    (text : String) (number : Nat) (value : Value) : Script :=
  ⟨[(originalLookup (tableReference tableName alias) idName sourceName text number, [value])]⟩

/-- The lookup {lit}`SELECT id FROM t WHERE stored = lower(?n)` over the new field as a query script with
the value bound to its parameter. -/
def storedLookupScript (tableName : Identifier) (alias : Option Identifier) (idName storedName : Identifier)
    (text : String) (number : Nat) (value : Value) : Script :=
  ⟨[(storedLookup (tableReference tableName alias) idName storedName text number, [value])]⟩

/-- For every site of the lowercase expansion, the value assigned by the backfill is the lowercase of the
source column. Proof sketch: the written value mentions the source column, so the assignment keeps the
resolved expression ({name}`assignedExpression_of_mentions`). -/
theorem LowercaseSite.assigned_eq {database : Database.Raw} {tableName idName sourceName storedName : Identifier}
    (site : LowercaseSite database tableName idName sourceName storedName) :
    site.toSite.assigned = .scalar .lower (.cons (.column site.source) .nil) := by
  have sourceAppended := columnPosition_append site.sourceFound [textColumn storedName site.table.shape.strict]
  have identifier := mentionsColumn_identifier_singleAt (position := some site.position) (tableName := tableName)
    (rowid := !site.table.shape.withoutRowid) (aliased := false) .none sourceAppended
  have call (scope : Scope) :
      mentionsColumn scope (lowerCall sourceName) = mentionsColumn scope (.identifier sourceName .none) := by
    simp [lowerCall, mentionsColumn, mentionsColumnIn]
  exact assignedExpression_of_mentions (by rw [call]; exact identifier)

/-- For every site of the lowercase expansion, every alias of the table, text and parameter number, value
and list of triggers, the original lookup is moved to the stored lookup: the two resolve to simple queries
with the original and stored filters, the queries are calm, and on each row of the table the stored filter
on the row with the lowercase cell appended keeps the row exactly when the original filter keeps it. Proof
sketch: resolution by {name}`resolve_original_lookup` and {name}`resolve_stored_lookup`; the agreement is
{name}`storedFilter_append` for the bound parameters. -/
def LowercaseSite.lookupMove {database : Database.Raw} {tableName idName sourceName storedName : Identifier}
    (site : LowercaseSite database tableName idName sourceName storedName) (alias : Option Identifier)
    (text : String) (number : Nat) (value : Value) (triggers : List (Identifier × CatalogTrigger)) :
    site.toSite.LookupMove triggers (originalLookup (tableReference tableName alias) idName sourceName text number)
      (storedLookup (tableReference tableName alias) idName storedName text number) [value] :=
  have idInside := columnPosition_lt site.idFound
  have strict : (textColumn storedName site.table.shape.strict).affinity = .text := textColumn_affinity _ _
  { beforeFilter := some (originalFilter site.source number)
    afterFilter := some (storedFilter site.table.shape.columns.length number)
    columns := [.scalar (.column site.id)]
    columnsBelow := by
      intro output member
      cases List.mem_singleton.mp member
      simp [Output.readsBelow, Expr.readsBelow, Expr.any, Expr.isColumnFrom]
      exact idInside
    resolvesBefore := fun state same => by
      obtain ⟨names, resolved⟩ := resolve_original_lookup runContext state (tableReference tableName alias)
        site.position site.table.shape idName sourceName text number rfl rfl rfl (by rw [same]; exact site.found)
        site.idFound site.sourceFound
      exact ⟨names, state, resolved⟩
    resolvesAfter := fun state same => by
      have extended : state.catalog.findTable tableName = some (site.position,
          { site.table.shape with columns := site.table.shape.columns ++ [textColumn storedName site.table.shape.strict] }) := by
        rw [same]
        have := Database.findTable_addDerivedColumn (site.toSite.column) site.toSite.assigned triggers site.found
        simpa [DerivedColumnMigration.Site.reached, DerivedColumnMigration.Site.column, LowercaseSite.toSite,
          Table.addDerivedColumn, definedColumn_text] using this
      obtain ⟨names, resolved⟩ := resolve_stored_lookup runContext state (tableReference tableName alias)
        site.position _ idName storedName text number rfl rfl rfl extended
        (columnPosition_append site.idFound _) (columnPosition_append_new site.fresh (by simp [textColumn]))
        (by simp [strict]) (by simp [textColumn])
      exact ⟨names, state, resolved⟩
    calmBefore := fun names => simpleColumn_calm _ _ _ names (originalFilter_calm _ _)
    calmAfter := fun names => simpleColumn_calm _ _ _ names (storedFilter_calm _ _)
    agree := fun wide => by
      intro cells member
      have width := sourceRows_width wide cells member
      have affinity : site.toSite.column.affinity = .text := by
        simp [DerivedColumnMigration.Site.column, LowercaseSite.toSite, definedColumn_text, strict]
      have stored : Value.store site.toSite.column.affinity
          (site.toSite.assigned.eval (EvalContext.plain 0) cells) = mapText lowerByte (cells.getD site.source .null) := by
        rw [affinity, site.assigned_eq]
        exact store_lower _
      simp only [Option.all_some, stored]
      exact congrArg truthy
        (storedFilter_append (EvalContext.bound [value]) (fun _ _ _ => rfl) cells _ site.source number width) }

/-- For every site of the lowercase expansion, every alias of the table, text and parameter number and
list of triggers, the original lookup is kept as it is: it resolves to the same simple query before and
after the migration, its filter and its id column read only old columns, and it is calm. Proof sketch:
{name}`resolve_original_lookup` on the table before and after (the source and id columns keep their
positions when a column is appended). -/
def LowercaseSite.originalPreserved {database : Database.Raw}
    {tableName idName sourceName storedName : Identifier}
    (site : LowercaseSite database tableName idName sourceName storedName) (alias : Option Identifier)
    (text : String) (number : Nat) (triggers : List (Identifier × CatalogTrigger)) :
    site.toSite.ReadPreserved triggers (originalLookup (tableReference tableName alias) idName sourceName text number) :=
  have idInside := columnPosition_lt site.idFound
  have sourceInside := columnPosition_lt site.sourceFound
  { filter := some (originalFilter site.source number)
    columns := [.scalar (.column site.id)]
    filterBelow := by
      intro condition member
      cases Option.mem_some_iff.mp member
      simp [originalFilter, Expr.readsBelow, Expr.any, Arguments.any, Expr.isColumnFrom]
      exact sourceInside
    columnsBelow := by
      intro output member
      cases List.mem_singleton.mp member
      simp [Output.readsBelow, Expr.readsBelow, Expr.any, Expr.isColumnFrom]
      exact idInside
    resolvesBefore := fun state same => by
      obtain ⟨names, resolved⟩ := resolve_original_lookup runContext state (tableReference tableName alias)
        site.position site.table.shape idName sourceName text number rfl rfl rfl (by rw [same]; exact site.found)
        site.idFound site.sourceFound
      exact ⟨names, state, resolved⟩
    resolvesAfter := fun state same => by
      have extended : state.catalog.findTable tableName = some (site.position,
          { site.table.shape with columns := site.table.shape.columns ++ [textColumn storedName site.table.shape.strict] }) := by
        rw [same]
        have := Database.findTable_addDerivedColumn (site.toSite.column) site.toSite.assigned triggers site.found
        simpa [DerivedColumnMigration.Site.reached, DerivedColumnMigration.Site.column, LowercaseSite.toSite,
          Table.addDerivedColumn, definedColumn_text] using this
      obtain ⟨names, resolved⟩ := resolve_original_lookup runContext state (tableReference tableName alias)
        site.position _ idName sourceName text number rfl rfl rfl extended
        (columnPosition_append site.idFound _) (columnPosition_append site.sourceFound _)
      exact ⟨names, state, resolved⟩
    calm := fun names => simpleColumn_calm _ _ _ names (originalFilter_calm _ _) }

/-- For every table, names, text, number, value and triggers of the lowercase expansion, on every valid
database that has a {name}`LowercaseSite`, in every complete environment, if the expansion succeeds on
every raw and concrete branch, then the original lookup {lit}`WHERE lower(source) = lower(?n)` before it
and the stored lookup {lit}`WHERE stored = lower(?n)` after it have equal actual values and traces and the
same set of branch observations. Plain words: for every such database, environment and bound value, the
lookup through the lowercase field after the expansion gives the ids that the lookup through
{lit}`lower(source)` gives before it. Proof sketch: the general
{lit}`DerivedColumnMigration.queryTranslates` with the site {name}`LowercaseSite.toSite` and the move
{name}`LowercaseSite.lookupMove`. -/
theorem queryTranslates (tableName : Identifier) (alias : Option Identifier)
    (idName sourceName storedName : Identifier) (text : String) (number : Nat) (value : Value)
    (first second : Identifier × CatalogTrigger) (firstValues secondValues thirdValues fourthValues : List Value) :
    Migration.QueryTranslates
      (send (expansion tableName storedName sourceName first second firstValues secondValues thirdValues
        fourthValues))
      (originalLookupScript tableName alias idName sourceName text number value)
      (storedLookupScript tableName alias idName storedName text number value)
      (fun db => Nonempty (LowercaseSite db.raw tableName idName sourceName storedName))
      (by simp [Script.isQuery, originalLookupScript, originalLookup, Syntax.Statement.readsOnly])
      (by simp [Script.isQuery, storedLookupScript, storedLookup, Syntax.Statement.readsOnly]) :=
  DerivedColumnMigration.queryTranslates tableName (textDefinition storedName) (lowerCall sourceName)
    firstValues secondValues [(first, thirdValues), (second, fourthValues)]
    (originalLookup (tableReference tableName alias) idName sourceName text number)
    (storedLookup (tableReference tableName alias) idName storedName text number) [value] rfl rfl rfl rfl
    (fun db => Nonempty (LowercaseSite db.raw tableName idName sourceName storedName))
    (fun _ inside => (Classical.choice inside).toSite)
    (fun _ inside => (Classical.choice inside).lookupMove alias text number value _)

/-- For every table, names, text, number, value and triggers of the lowercase expansion, on every valid
database that has a {name}`LowercaseSite`, in every complete environment, if the expansion succeeds, then
the lookup {lit}`WHERE lower(source) = lower(?n)` gives the same actual value and trace and the same set of
branch observations after the expansion as before it. Proof sketch: the general
{lit}`DerivedColumnMigration.queryPreserves` with the read {name}`LowercaseSite.originalPreserved`. -/
theorem queryPreserves (tableName : Identifier) (alias : Option Identifier)
    (idName sourceName storedName : Identifier) (text : String) (number : Nat) (value : Value)
    (first second : Identifier × CatalogTrigger) (firstValues secondValues thirdValues fourthValues : List Value) :
    Migration.QueryPreserves
      (send (expansion tableName storedName sourceName first second firstValues secondValues thirdValues
        fourthValues))
      (originalLookupScript tableName alias idName sourceName text number value)
      (fun db => Nonempty (LowercaseSite db.raw tableName idName sourceName storedName))
      (by simp [Script.isQuery, originalLookupScript, originalLookup, Syntax.Statement.readsOnly]) :=
  DerivedColumnMigration.queryPreserves tableName (textDefinition storedName) (lowerCall sourceName)
    firstValues secondValues [(first, thirdValues), (second, fourthValues)]
    (originalLookup (tableReference tableName alias) idName sourceName text number) [value] rfl rfl
    (fun db => Nonempty (LowercaseSite db.raw tableName idName sourceName storedName))
    (fun _ inside => (Classical.choice inside).toSite)
    (fun _ inside => (Classical.choice inside).originalPreserved alias text number _)

end LowercaseFixture
