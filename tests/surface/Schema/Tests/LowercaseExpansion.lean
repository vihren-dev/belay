import LowercaseLookups

set_option doc.verso true

/-! The guide's lowercase-field expansion as an instance of the general derived-column migration
(ADR 0017, S6): add a plain TEXT field, fill it with the lowercase of an existing column, and register two
triggers. The general migration ({lit}`Belay.Sqlite.DerivedColumnMigration`) takes any column definition and
any written value. This module fixes them to {lit}`TEXT` and {lit}`lower(source)`, and builds the general
{lit}`Site` of the migration from the facts that the guide's table has: an id column, a source column and
no column of the new name. -/

namespace LowercaseFixture
open Belay.Sqlite Belay.Sqlite.Model Belay.Sqlite.Model.Resolved

/-- The written value {lit}`lower(source)`. -/
def lowerCall (sourceName : Identifier) : Syntax.Expr := .call "lower" [.identifier sourceName .none]

/-- The table named in {lit}`FROM` with an optional alias and no function arguments or derived source. -/
def tableReference (tableName : Identifier) (alias : Option Identifier := none) : Syntax.TableReference :=
  { table := tableName, alias }

/-- The four-statement expansion script for the table {lit}`tableName`: ADD the plain TEXT field
{lit}`name`, set it to the lowercase of the column {lit}`sourceName` for every row, then create the two
triggers. The trigger names and definitions, and the values bound to each statement, are arbitrary. It is
the general migration with a TEXT definition and the written value {name}`lowerCall`. -/
def expansion (tableName name sourceName : Identifier) (first second : Identifier × CatalogTrigger)
    (firstValues secondValues thirdValues fourthValues : List Value) : Script :=
  DerivedColumnMigration.migration tableName (textDefinition name) (lowerCall sourceName) firstValues secondValues
    [(first, thirdValues), (second, fourthValues)]

/-- A database has a table into which a plain TEXT field can be added and filled by a migration: the table is
physical, found by name at a catalog position, has an id column, and no column of the new name. Its primary-key
positions lie inside its columns, its columns are plain (not generated), and the catalog with the new field
added selects no trigger for an UPDATE of that field. Other tables, indexes, triggers and rows are
unrestricted. The facts say nothing about the written value that fills the field. -/
structure TextFieldSite (database : Database.Raw) (tableName idName storedName : Identifier) where
  /-- The catalog position of the table. -/
  position : Nat
  /-- The table with its rows. -/
  table : Table
  /-- The position of the id column. -/
  id : Nat
  /-- The catalog finds the table by name at the position. -/
  found : database.catalog.findTable tableName = some (position, table.shape)
  /-- The database has this table at the position. -/
  present : database.table position = some table
  /-- No column has the new name. -/
  fresh : columnPosition table.shape.columns storedName = none
  /-- The id column is at its position. -/
  idFound : columnPosition table.shape.columns idName = some id
  /-- Every primary-key position is a column of the table. -/
  keysInside : ∀ key ∈ table.shape.primaryKey, key < table.shape.columns.length
  /-- No original column is generated. -/
  plain : ∀ old ∈ table.shape.columns, old.generated = none
  /-- With the new column added, the catalog selects no trigger for an UPDATE of that column. -/
  noneFiring : (database.catalog.addColumn position (textColumn storedName table.shape.strict)).triggersFiring
    { table := position, event := .update (some [table.shape.columns.length]) } = []

/-- A {name}`TextFieldSite` whose table also has the column that the lowercase expansion reads: the source
column is at its position. -/
structure LowercaseSite (database : Database.Raw) (tableName idName sourceName storedName : Identifier)
    extends TextFieldSite database tableName idName storedName where
  /-- The position of the source column. -/
  source : Nat
  /-- The source column is at its position. -/
  sourceFound : columnPosition table.shape.columns sourceName = some source

/-- For every table shape and name, a plain TEXT declaration is admitted by the table: the statement has
no generated column, no misplaced deferral and, in a STRICT table, TEXT is a strict type. -/
theorem addColumnRestriction_text (shape : CatalogTable) (name : Identifier) :
    addColumnRestriction shape (textDefinition name) = none := by
  change (if shape.strict && false then some RestrictionKind.addColumnStrictType else none) = none
  simp

/-- The general site of the migration, from the guide's facts. The written value resolves to the lowercase
call of the source column, which mentions a column and so is stored as written, and which reads only old
columns. Proof sketch: each field of the general site is one of the guide's facts, or follows from the
resolution laws of {lit}`LowercaseLookups`. -/
def LowercaseSite.toSite {database : Database.Raw} {tableName idName sourceName storedName : Identifier}
    (site : LowercaseSite database tableName idName sourceName storedName) :
    DerivedColumnMigration.Site database tableName (textDefinition storedName) (lowerCall sourceName) :=
  have sourceAppended := columnPosition_append site.sourceFound [textColumn storedName site.table.shape.strict]
  have mentions : mentionsColumn (backfillScope site.position tableName site.table.shape
      (definedColumn site.table.shape.strict (textDefinition storedName))) (lowerCall sourceName) = true := by
    rw [definedColumn_text]
    have identifier := mentionsColumn_identifier_singleAt (position := some site.position) (tableName := tableName)
      (rowid := !site.table.shape.withoutRowid) (aliased := false) .none sourceAppended
    have call (scope : Scope) :
        mentionsColumn scope (lowerCall sourceName) = mentionsColumn scope (.identifier sourceName .none) := by
      simp [lowerCall, mentionsColumn, mentionsColumnIn]
    rw [call]
    exact identifier
  { position := site.position, table := site.table
    derived := .scalar .lower (.cons (.column site.source) .nil), affinity := none
    found := site.found, present := site.present, constraintFree := rfl
    admitted := addColumnRestriction_text _ _
    fresh := site.fresh
    operand := by
      rw [definedColumn_text]
      exact resolve_lower_column_at sourceAppended
    below := by
      have inside := columnPosition_lt site.sourceFound
      simp [Expr.readsBelow, Expr.any, Arguments.any, Expr.isColumnFrom, inside]
    contextFree := by
      rw [assignedExpression_of_mentions mentions]
      intro first second cells
      rfl
    keysInside := site.keysInside, plain := site.plain
    noneFiring := by rw [definedColumn_text]; exact site.noneFiring }

end LowercaseFixture
