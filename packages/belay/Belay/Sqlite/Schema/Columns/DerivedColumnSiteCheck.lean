import Belay.Sqlite.Schema.Columns.DerivedColumnMigration

set_option doc.verso true

/-! A computed check of the {lit}`Site` of a derived-column migration on a catalog. All facts of a site
except the rows of the table depend on the catalog only, so the check runs once on the catalog of a
schema, and the kernel can evaluate it. {lit}`Site.ofCheck` then gives the site for every database with
that catalog, with the rows of the database. -/

namespace Belay.Sqlite.DerivedColumnMigration
open Belay.Sqlite.Model

/-- Whether a node of a resolved expression reads anything other than its row: the clock, a counter, an
aggregate value, a subquery or a parameter ({name}`Resolved.Expr.readsBeyondRowAndParameters`, or a
parameter). Other nodes return false; {name}`Resolved.Expr.any` checks their operands. For example, the
column node of {lit}`lower(email)` returns false, and the node of {lit}`?1` returns true. -/
def readsBeyondRow (node : Resolved.Expr) : Bool :=
  node.readsBeyondRowAndParameters || node matches .parameter _

/-- For every resolved expression with no node that {name}`readsBeyondRow` finds, the expression is
context-free ({name}`Resolved.Expr.ContextFree`): every two evaluation contexts give it the same value
on every row. Proof sketch: {name}`Resolved.Expr.evaluate_congr` with the nodes of {name}`readsBeyondRow`
masked; every node that remains reads only the row. -/
theorem contextFree_of_rowOnly {expression : Resolved.Expr} (rowOnly : expression.any readsBeyondRow = false) :
    expression.ContextFree := by
  intro first second cells
  refine congrArg Prod.fst (Resolved.Expr.evaluate_congr first second cells cells readsBeyondRow ?_ expression
    rowOnly).1
  intro node allowed
  cases node <;> simp_all [readsBeyondRow, Resolved.Expr.readsBeyondRowAndParameters, Resolved.Expr.ReadsAgree]

/-- The parts of a site that the catalog gives: the position and shape of the table that has the name,
and the resolved written value with its affinity, in the scope of the table with the added column. None
when the catalog has no table of the name or the value does not resolve. -/
def siteParts (catalog : Catalog) (tableName : Identifier) (definition : Syntax.ColumnDefinition)
    (value : Syntax.Expr) : Option (Nat × CatalogTable × Resolved.Expr × Option Affinity) :=
  match catalog.findTable tableName with
  | none => none
  | some (position, shape) =>
    match resolveOperand runContext.profile.dqsDml
        (backfillScope position tableName shape (definedColumn shape.strict definition)) {} true value with
    | .ok (derived, affinity) => some (position, shape, derived, affinity)
    | .error _ => none

/-- For every catalog, migration parts and site parts that {name}`siteParts` gives, the catalog finds the
table at the position with the shape, and the written value resolves to the expression with the affinity.
Proof sketch: unfold the two matches. -/
theorem siteParts_some {catalog : Catalog} {tableName : Identifier} {definition : Syntax.ColumnDefinition}
    {value : Syntax.Expr} {position : Nat} {shape : CatalogTable} {derived : Resolved.Expr}
    {affinity : Option Affinity}
    (parts : siteParts catalog tableName definition value = some (position, shape, derived, affinity)) :
    catalog.findTable tableName = some (position, shape) ∧
      resolveOperand runContext.profile.dqsDml
        (backfillScope position tableName shape (definedColumn shape.strict definition)) {} true value =
          .ok (derived, affinity) := by
  unfold siteParts at parts
  split at parts
  · cases parts
  · rename_i found
    split at parts
    · rename_i resolved
      cases parts
      exact ⟨found, resolved⟩
    · cases parts

/-- The facts of a site that the catalog decides, for the site parts of {name}`siteParts`. It is true
when all of these hold:

* the column definition has no constraint, the table admits its type, and no column has its name;
* the resolved value reads only old columns, and the stored expression reads only the row
  ({name}`readsBeyondRow`): no clock, counter, parameter, aggregate value or subquery;
* every primary-key position is a column, and no column is generated;
* with the column added, the catalog selects no trigger for an UPDATE of the column.

It is a sufficient check: a value such as {lit}`coalesce(0, ?1)` reads a parameter and fails it, although
its stored expression is context-free. Build such a {name}`Site` by hand. -/
def siteFacts (catalog : Catalog) (tableName : Identifier) (definition : Syntax.ColumnDefinition)
    (value : Syntax.Expr) : Nat × CatalogTable × Resolved.Expr × Option Affinity → Bool
  | (position, shape, derived, _) =>
    definition.constraints.isEmpty && (addColumnRestriction shape definition).isNone &&
      (columnPosition shape.columns definition.name).isNone && derived.readsBelow shape.columns.length &&
      !(assignedExpression (backfillScope position tableName shape (definedColumn shape.strict definition))
        shape.columns.length value derived).any readsBeyondRow &&
      shape.primaryKey.all (· < shape.columns.length) && shape.columns.all (·.generated.isNone) &&
      ((catalog.addColumn position (definedColumn shape.strict definition)).triggersFiring
        { table := position, event := .update (some [shape.columns.length]) }).isEmpty

/-- Whether the catalog gives a {name}`Site` for the migration parts: {name}`siteParts` finds the parts,
and {name}`siteFacts` holds for them. For example, for a table {lit}`customers` with a column
{lit}`email`, the value {lit}`lower(email)` and a new column {lit}`email_lower TEXT`, the check is true;
with a value that reads the clock or a parameter, or a new column that has a NOT NULL constraint, it is
false. -/
def siteCheck (catalog : Catalog) (tableName : Identifier) (definition : Syntax.ColumnDefinition)
    (value : Syntax.Expr) : Bool :=
  match siteParts catalog tableName definition value with
  | some parts => siteFacts catalog tableName definition value parts
  | none => false

/-- The {name}`Site` of the migration parts on every database whose catalog passes {name}`siteCheck`. The
table is the table of the catalog, with the rows of the database at its position. -/
def Site.ofCheck {database : Database.Raw} {catalog : Catalog} {tableName : Identifier}
    {definition : Syntax.ColumnDefinition} {value : Syntax.Expr} (same : database.catalog = catalog)
    (checked : siteCheck catalog tableName definition value = true) : Site database tableName definition value :=
  match parts : siteParts catalog tableName definition value, checked with
  | none, checked => absurd checked (by simp [siteCheck, parts])
  | some (position, shape, derived, affinity), checked =>
    have facts : siteFacts catalog tableName definition value (position, shape, derived, affinity) = true := by
      simpa [siteCheck, parts] using checked
    have found := (siteParts_some parts).1
    have resolved := (siteParts_some parts).2
    have holds := facts
    { position, table := { shape, rows := database.rows.getD position [] }, derived, affinity
      found := same ▸ found
      present := database.table_of_findTable tableName position shape (same ▸ found)
      constraintFree := by simp_all [siteFacts]
      admitted := by simp_all [siteFacts]
      fresh := by simp_all [siteFacts]
      operand := resolved
      below := by simp_all [siteFacts]
      contextFree := contextFree_of_rowOnly (by simp_all [siteFacts])
      keysInside := by simp_all [siteFacts]
      plain := by simp_all [siteFacts]
      noneFiring := by rw [same]; simp_all [siteFacts] }

/-- For every site that {name}`Site.ofCheck` gives, the position of the site is the position that
{name}`siteParts` gives, and the shape of its table is the shape of the catalog. Proof sketch: unfold the
match of the builder. -/
theorem Site.ofCheck_parts {database : Database.Raw} {catalog : Catalog} {tableName : Identifier}
    {definition : Syntax.ColumnDefinition} {value : Syntax.Expr} (same : database.catalog = catalog)
    (checked : siteCheck catalog tableName definition value = true) :
    siteParts catalog tableName definition value =
      some ((Site.ofCheck same checked).position, (Site.ofCheck same checked).table.shape,
        (Site.ofCheck same checked).derived, (Site.ofCheck same checked).affinity) := by
  unfold Site.ofCheck
  split
  next holds _ parts => simp [siteCheck, parts] at holds
  next _ _ _ _ _ _ parts => exact parts

end Belay.Sqlite.DerivedColumnMigration
