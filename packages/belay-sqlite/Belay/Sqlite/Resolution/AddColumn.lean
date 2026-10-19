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
SQLite, resolved once ({name}`resolveColumnDefault`). A DEFAULT that the model does not
describe gives {lean}`(none : Option CatalogColumn)`. Key constraints leave this metadata
unchanged; callers must reject them before using this helper. -/
def addedColumn (definition : Syntax.ColumnDefinition) : Option CatalogColumn :=
  definition.constraints.foldlM (fun column constraint => match constraint with
    | .notNull algorithm => some { column with notNull := true, notNullAlgorithm := algorithm.getD .abort }
    | .default expression sourceText =>
      (resolveColumnDefault column.affinity ⟨expression, sourceText⟩).map fun resolved =>
        { column with defaultValue := some resolved }
    | .collate name => (Collation.named? name).map fun collation => { column with collation }
    | .primaryKey .. | .unique _ | .check .. | .references .. | .generated .. => some column)
    { name := definition.name, declaredType := reportedType definition.declaredType }

/-- Resolve ALTER TABLE ADD COLUMN. Path 1 is the column definition. Its CHECK constraints
resolve over the table with the new column ({name}`columnChecks`); one that SQLite cannot
resolve is {name}`RestrictionKind.addColumnCheckError`, as SQLite reports it while the
statement runs. Its {lit}`REFERENCES` constraints are its foreign keys. -/
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
    else if definition.constraints.any (· matches .generated ..) then restrict index [1] .addColumnGenerated
    else
      match addedColumn definition with
      | none => restrict index [1] .addColumnConstraint
      | some column =>
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
