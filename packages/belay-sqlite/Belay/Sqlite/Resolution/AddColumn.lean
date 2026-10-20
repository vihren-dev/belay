import Belay.Sqlite.Resolution.Definitions

set_option doc.verso true

/-! Name resolution of ALTER TABLE ADD COLUMN. The prepare checks follow the order of
SQLite 3.51.0's {lit}`sqlite3AlterBeginAddColumn`, {lit}`sqlite3AddColumn`, the constraint
actions and {lit}`sqlite3AlterFinishAddColumn`, because SQLite reports the first error it
finds. Model restrictions follow the prepare checks. -/

namespace Belay.Sqlite

/-- Construct added-column metadata after PRIMARY KEY and UNIQUE have been
rejected. NOT NULL sets nullability and its {lit}`ON CONFLICT` algorithm (ABORT without
one), as in CREATE TABLE, and each written DEFAULT replaces the preceding default, as in
SQLite, resolved once ({name}`resolveColumnDefault`) with the affinity of the column, which
has the strict type of a {lit}`STRICT` table ({name}`definedColumn`). A DEFAULT that the model does not
describe gives {lean}`(none : Option CatalogColumn)`. Key constraints leave this metadata
unchanged; callers must reject them before using this helper. -/
def addedColumn (strict : Bool) (definition : Syntax.ColumnDefinition) : Option CatalogColumn :=
  definition.constraints.foldlM (fun column constraint => match constraint with
    | .notNull algorithm => some { column with notNull := true, notNullAlgorithm := algorithm.getD .abort }
    | .default expression sourceText =>
      (resolveColumnDefault column.affinity ⟨expression, sourceText⟩).map fun resolved =>
        { column with defaultValue := some resolved }
    | .collate name => (Collation.named? name).map fun collation => { column with collation }
    | .primaryKey .. | .unique _ | .check .. | .references .. | .generated .. => some column)
    (definedColumn strict definition)

/-- The model restriction of an added column that SQLite checks only while ADD COLUMN runs, or
none: a generated column is {name}`RestrictionKind.addColumnGenerated`, and a column of a
{lit}`STRICT` table without a type that it admits ({name}`StrictType.ofReported`) is
{name}`RestrictionKind.addColumnStrictType`, as is a default that does not fit the type
({lit}`strictDefaultFits`, after the column is built). -/
def addColumnRestriction (table : CatalogTable) (definition : Syntax.ColumnDefinition) : Option RestrictionKind :=
  if definition.constraints.any (· matches .generated ..) then some .addColumnGenerated
  else if table.strict && (StrictType.ofReported (reportedType definition.declaredType)).isNone then
    some .addColumnStrictType
  else none

/-- Whether the default of an added column fits its strict type ({name}`StrictType.fits`): a
column without a strict type, or with a time default, fits. SQLite checks the default of a
{lit}`STRICT` table's column only while ADD COLUMN runs, as {lit}`type mismatch on DEFAULT`
when the table has rows (checked natively with 3.51.0). -/
def strictDefaultFits (column : CatalogColumn) : Bool :=
  match column.strictType, readDefaultValue column with
  | some strictType, .ok value => strictType.fits value
  | some _, .error _ | none, _ => true

/-- Resolve ALTER TABLE ADD COLUMN. Path 1 is the column definition. Its CHECK constraints
resolve over the table with the new column ({name}`columnChecks`); one that SQLite cannot
resolve is {name}`RestrictionKind.addColumnCheckError`, as SQLite reports it while the
statement runs. A default that does not fit the column's strict type
({name}`strictDefaultFits`) is {name}`RestrictionKind.addColumnStrictType`. Its
{lit}`REFERENCES` constraints are its foreign keys. -/
def resolveAddColumn (context : ResolveContext) (catalog : Catalog) (index : Nat)
    (tableName : Identifier) (definition : Syntax.ColumnDefinition) : StatementResolution :=
  match catalog.findTable tableName with
  | none => prepareError catalog (.noSuchTable tableName)
  | some (position, table) =>
    if reservedName tableName then prepareError catalog (.expression (.tableMayNotBeAltered tableName))
    else if table.columns.length + 1 > context.profile.limits.columns then
      prepareError catalog (.expression (.tooManyColumns tableName))
    else if (columnPosition table.columns definition.name).isSome then
      prepareError catalog (.expression (.duplicateColumn definition.name))
    else if let some error := definition.constraints.findSome? (·.parseError definition.name) then
      prepareError catalog (.expression error)
    else if definition.constraints.any Syntax.ColumnConstraint.isPrimaryKey && !table.primaryKey.isEmpty then
      prepareError catalog (.expression (.multiplePrimaryKeys tableName))
    else if definition.constraints.any Syntax.ColumnConstraint.nonconstantDefault then
      prepareError catalog (.expression (.defaultNotConstant definition.name))
    else if definition.constraints.any Syntax.ColumnConstraint.isPrimaryKey then prepareError catalog (.expression .cannotAddPrimaryKey)
    else if definition.constraints.any Syntax.ColumnConstraint.isUnique then prepareError catalog (.expression .cannotAddUnique)
    else if rowidName definition.name then restrict index [1] .rowidColumnName
    else match addColumnRestriction table definition with
    | some kind => restrict index [1] kind
    | none =>
      match addedColumn table.strict definition with
      | none => restrict index [1] .addColumnConstraint
      | some column =>
        if !strictDefaultFits column then restrict index [1] .addColumnStrictType else
        let scope := Scope.single tableName (table.columns ++ [column]) !table.withoutRowid
        match columnChecks context.profile.dqsDdl scope definition with
        | .error (.prepare _) => restrict index [1] .addColumnCheckError
        | .error (.restriction path reason) => restrict index (1 :: path) reason
        | .ok checks =>
          let foreignKeys := definition.constraints.filterMap fun
            | .references target columns onDelete onUpdate =>
              some { table := target, columns := [table.columns.length], referenced := columns, onDelete, onUpdate }
            | .notNull _ | .primaryKey .. | .unique _ | .default .. | .collate _ | .check .. | .generated .. => none
          let column := { column with checks, foreignKeys }
          .ok (.addColumn position column, catalog.addColumn position column)

end Belay.Sqlite
