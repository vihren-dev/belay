import ConcatFilters

set_option doc.verso true

/-! The migration that stores the concatenation of two columns in a plain TEXT field, as an instance of the general
derived-column laws (ADR 0017, S6). The general migration takes any written value. This module fixes it to
{lit}`a || b`, builds the site of the migration from the facts that a table with the three columns has, moves the
lookup {lit}`WHERE a || b = lower(?n)` to {lit}`WHERE stored = lower(?n)`, and derives the claim for every
database that has the site. It shows that the general laws are not tied to {lit}`lower`. -/

namespace ConcatFixture
open Belay.Sqlite Belay.Sqlite.Model Belay.Sqlite.Model.Resolved LowercaseFixture

/-- The written value {lit}`a || b`. -/
def pipesWritten (firstName secondName : Identifier) : Syntax.Expr :=
  .concatenate (.identifier firstName .none) (.identifier secondName .none)

/-- A {name}`TextFieldSite` whose table has the two columns that the migration concatenates. -/
structure ConcatSite (database : Database.Raw) (tableName idName firstName secondName storedName : Identifier)
    extends TextFieldSite database tableName idName storedName where
  /-- The position of the first column. -/
  first : Nat
  /-- The position of the second column. -/
  second : Nat
  /-- The first column is at its position. -/
  firstFound : columnPosition table.shape.columns firstName = some first
  /-- The second column is at its position. -/
  secondFound : columnPosition table.shape.columns secondName = some second

/-- For every site of the concatenation migration, the written value {lit}`a || b` mentions a column of the
table in the scope of the backfill, so the backfill stores the resolved expression as written. Proof sketch:
the first operand is a column of the scope, found by {name}`mentionsColumn_identifier_singleAt`. -/
theorem ConcatSite.mentions {database : Database.Raw} {tableName idName firstName secondName storedName : Identifier}
    (site : ConcatSite database tableName idName firstName secondName storedName) :
    mentionsColumn (backfillScope site.position tableName site.table.shape
      (definedColumn site.table.shape.strict (textDefinition storedName))) (pipesWritten firstName secondName) =
        true := by
  have firstAppended := columnPosition_append site.firstFound [textColumn storedName site.table.shape.strict]
  rw [definedColumn_text]
  have identifier := mentionsColumn_identifier_singleAt (position := some site.position) (tableName := tableName)
    (rowid := !site.table.shape.withoutRowid) (aliased := false) .none firstAppended
  simp [pipesWritten, mentionsColumn] at identifier ⊢
  exact Or.inl identifier

/-- The general site of the migration, from the facts of the table. The written value resolves to the
concatenation of the two columns, which mentions a column and so is stored as written, and which reads only
old columns. Proof sketch: each field of the general site is one of the facts, or follows from the resolution
laws of {lit}`ConcatFilters`. -/
def ConcatSite.toSite {database : Database.Raw} {tableName idName firstName secondName storedName : Identifier}
    (site : ConcatSite database tableName idName firstName secondName storedName) :
    DerivedColumnMigration.Site database tableName (textDefinition storedName) (pipesWritten firstName secondName) :=
  have firstAppended := columnPosition_append site.firstFound [textColumn storedName site.table.shape.strict]
  have secondAppended := columnPosition_append site.secondFound [textColumn storedName site.table.shape.strict]
  { position := site.position, table := site.table
    derived := pipesCall site.first site.second, affinity := none
    found := site.found, present := site.present, constraintFree := rfl
    admitted := addColumnRestriction_text _ _
    fresh := site.fresh
    operand := by
      rw [definedColumn_text]
      exact resolve_pipes_at firstAppended secondAppended
    below := by
      have firstInside := columnPosition_lt site.firstFound
      have secondInside := columnPosition_lt site.secondFound
      simp [pipesCall, Expr.readsBelow, Expr.any, Arguments.any, Expr.isColumnFrom, firstInside, secondInside]
    contextFree := by
      rw [assignedExpression_of_mentions site.mentions]
      intro first second cells
      rfl
    keysInside := site.keysInside, plain := site.plain
    noneFiring := by rw [definedColumn_text]; exact site.noneFiring }

/-- For every site of the concatenation migration, the value assigned by the backfill is the concatenation of
the two columns. Proof sketch: the written value mentions a column, so the assignment keeps the resolved
expression ({name}`assignedExpression_of_mentions`). -/
theorem ConcatSite.assigned_eq {database : Database.Raw} {tableName idName firstName secondName storedName : Identifier}
    (site : ConcatSite database tableName idName firstName secondName storedName) :
    site.toSite.assigned = pipesCall site.first site.second := by
  exact assignedExpression_of_mentions site.mentions

/-- For every site of the concatenation migration, every alias of the table, text, parameter number, value and
list of triggers, the lookup {lit}`WHERE a || b = lower(?n)` is moved to the stored lookup
{lit}`WHERE stored = lower(?n)`: the two resolve to simple queries with the two filters, the queries are calm,
and on each row of the table the stored filter on the row with the concatenation appended keeps the row exactly
when the original filter keeps it. Proof sketch: resolution by {name}`resolve_pipes_lookup` and
{name}`resolve_stored_lookup`; the agreement is {name}`storedFilter_append_pipes`. -/
def ConcatSite.lookupMove {database : Database.Raw} {tableName idName firstName secondName storedName : Identifier}
    (site : ConcatSite database tableName idName firstName secondName storedName) (alias : Option Identifier)
    (text : String) (number : Nat) (value : Value) (triggers : List (Identifier × CatalogTrigger)) :
    site.toSite.LookupMove triggers
      (pipesLookup (tableReference tableName alias) idName firstName secondName text number)
      (storedLookup (tableReference tableName alias) idName storedName text number) [value] :=
  have idInside := columnPosition_lt site.idFound
  have strict : (textColumn storedName site.table.shape.strict).affinity = .text := textColumn_affinity _ _
  { beforeFilter := some (pipesFilter site.first site.second number)
    afterFilter := some (storedFilter site.table.shape.columns.length number)
    columns := [.scalar (.column site.id)]
    columnsBelow := by
      intro output member
      cases List.mem_singleton.mp member
      simp [Output.readsBelow, Expr.readsBelow, Expr.any, Expr.isColumnFrom]
      exact idInside
    resolvesBefore := fun state same => by
      obtain ⟨names, resolved⟩ := resolve_pipes_lookup runContext state (tableReference tableName alias)
        site.position site.table.shape idName firstName secondName text number rfl rfl rfl
        (by rw [same]; exact site.found) site.idFound site.firstFound site.secondFound
      exact ⟨names, state, resolved⟩
    resolvesAfter := fun state same => by
      have extended : state.catalog.findTable tableName = some (site.position,
          { site.table.shape with
            columns := site.table.shape.columns ++ [textColumn storedName site.table.shape.strict] }) := by
        rw [same]
        have := Database.findTable_addDerivedColumn (site.toSite.column) site.toSite.assigned triggers site.found
        simpa [DerivedColumnMigration.Site.reached, DerivedColumnMigration.Site.column, ConcatSite.toSite,
          Table.addDerivedColumn, definedColumn_text] using this
      obtain ⟨names, resolved⟩ := resolve_stored_lookup runContext state (tableReference tableName alias)
        site.position _ idName storedName text number rfl rfl rfl extended
        (columnPosition_append site.idFound _) (columnPosition_append_new site.fresh (by simp [textColumn]))
        (by simp [strict]) (by simp [textColumn])
      exact ⟨names, state, resolved⟩
    calmBefore := fun names => simpleColumn_calm _ _ _ names (pipesFilter_calm _ _ _)
    calmAfter := fun names => simpleColumn_calm _ _ _ names (storedFilter_calm _ _)
    agree := fun wide => by
      intro cells member
      have width := sourceRows_width wide cells member
      have affinity : site.toSite.column.affinity = .text := by
        simp [DerivedColumnMigration.Site.column, ConcatSite.toSite, definedColumn_text, strict]
      have stored : Value.store site.toSite.column.affinity
          (site.toSite.assigned.eval (EvalContext.plain 0) cells) =
          pipesValue (cells.getD site.first .null) (cells.getD site.second .null) := by
        rw [affinity, site.assigned_eq]
        exact store_pipes _ _
      simp only [Option.all_some, stored]
      exact congrArg truthy
        (storedFilter_append_pipes (EvalContext.bound [value]) (fun _ _ _ => rfl) cells _ site.first site.second
          number width) }

/-- For every table, names, text, number, value, bound values and triggers, on every valid database that has a
{name}`ConcatSite`, in every complete environment, if the migration succeeds, then the lookup
{lit}`WHERE a || b = lower(?n)` before it and the stored lookup {lit}`WHERE stored = lower(?n)` after it have
equal actual values and traces and the same set of branch observations. Plain words: for every such database,
environment and bound value, looking up the ids through the stored concatenation after the migration gives the
ids that the concatenation gives before it. Proof sketch: the general
{lit}`DerivedColumnMigration.queryTranslates` with the site {name}`ConcatSite.toSite` and the move
{name}`ConcatSite.lookupMove`. -/
theorem concat_queryTranslates (tableName : Identifier) (alias : Option Identifier)
    (idName firstName secondName storedName : Identifier) (text : String) (number : Nat) (value : Value)
    (addValues updateValues : List Value) (triggers : List ((Identifier × CatalogTrigger) × List Value)) :
    Migration.QueryTranslates
      (send (DerivedColumnMigration.migration tableName (textDefinition storedName)
        (pipesWritten firstName secondName) addValues updateValues triggers))
      ⟨[(pipesLookup (tableReference tableName alias) idName firstName secondName text number, [value])]⟩
      ⟨[(storedLookup (tableReference tableName alias) idName storedName text number, [value])]⟩
      (fun db => Nonempty (ConcatSite db.raw tableName idName firstName secondName storedName))
      (by simp [Script.isQuery, pipesLookup, Syntax.Statement.readsOnly])
      (by simp [Script.isQuery, storedLookup, Syntax.Statement.readsOnly]) :=
  DerivedColumnMigration.queryTranslates tableName (textDefinition storedName) (pipesWritten firstName secondName)
    addValues updateValues triggers
    (pipesLookup (tableReference tableName alias) idName firstName secondName text number)
    (storedLookup (tableReference tableName alias) idName storedName text number) [value] rfl rfl rfl rfl
    (fun db => Nonempty (ConcatSite db.raw tableName idName firstName secondName storedName))
    (fun _ inside => (Classical.choice inside).toSite)
    (fun _ inside => (Classical.choice inside).lookupMove alias text number value _)

end ConcatFixture
