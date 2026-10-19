import Belay.Sqlite.Resolution.Context
import Belay.Sqlite.Resolution.KeyMerge
import Belay.Sqlite.Resolution.ReadDefaults
import Belay.Sqlite.Resolution.IndexTerms

set_option doc.verso true

/-! Name resolution of CREATE TABLE, CREATE INDEX and ALTER TABLE ADD COLUMN. The
prepare checks follow the order of SQLite 3.51.0's {lit}`sqlite3StartTable`,
{lit}`sqlite3AddColumn`, {lit}`sqlite3AddPrimaryKey`, {lit}`sqlite3CreateIndex` and
{lit}`sqlite3AlterFinishAddColumn`, because SQLite reports the first error it finds.
Model restrictions follow the prepare checks: a statement that SQLite refuses needs
no model. -/

namespace Belay.Sqlite

/-- The positions of key columns, or {lit}`no such column: %s` for the first name
that no column has. -/
def keyPositions (columns : List CatalogColumn) : List Identifier → Except ExprError (List Nat)
  | [] => .ok []
  | name :: rest => match columnPosition columns name with
    | some position => (keyPositions columns rest).map (position :: ·)
    | none => .error (.noSuchColumn name)

/-- Apply the function to the last element of a list; an empty list stays empty. -/
def updateLast (items : List α) (change : α → α) : List α :=
  match items with
  | [] => []
  | [last] => [change last]
  | first :: rest => first :: updateLast rest change

/-- Apply one column constraint of the last column of a table being created. -/
def applyConstraint (tableName : Identifier) (definition : Syntax.ColumnDefinition)
    (table : CatalogTable) : Syntax.ColumnConstraint → Except ExprError CatalogTable
  | .primaryKey descending algorithm =>
    if !table.primaryKey.isEmpty then .error (.multiplePrimaryKeys tableName) else
    let position := table.columns.length - 1
    let alias := if aliasesRowid definition.declaredType && !descending then some position else none
    setPrimaryKey table [position] alias descending algorithm
  | .default value sourceText =>
    if !constantDefault value then .error (.defaultNotConstant definition.name) else
    -- A default that the model does not describe leaves no default here; resolution then
    -- refuses the statement with {lit}`unmodeledDefault` ({lit}`modeledDefault`).
    .ok { table with columns := updateLast table.columns fun column =>
      { column with defaultValue := resolveColumnDefault column.affinity ⟨value, sourceText⟩ } }
  | .notNull algorithm => .ok { table with columns := updateLast table.columns fun column =>
      { column with notNull := true, notNullAlgorithm := algorithm.getD .abort } }
  | .unique algorithm => addUniqueKey table [table.columns.length - 1] algorithm

/-- Add the column definitions in written order: {lit}`too many columns on %s` when
a column would exceed the limit, then {lit}`duplicate column name: %s`, then each
column constraint ({lit}`sqlite3AddColumn` and the constraint actions). -/
def addDefinitions (limit : Nat) (tableName : Identifier) (table : CatalogTable) :
    List Syntax.ColumnDefinition → Except ExprError CatalogTable
  | [] => .ok table
  | definition :: rest => do
    if table.columns.length + 1 > limit then throw (.tooManyColumns tableName)
    if (columnPosition table.columns definition.name).isSome then
      throw (.duplicateColumn definition.name)
    let column : CatalogColumn := { name := definition.name, declaredType := reportedType definition.declaredType }
    let added := { table with columns := table.columns ++ [column] }
    let constrained ← definition.constraints.foldlM (applyConstraint tableName definition) added
    addDefinitions limit tableName constrained rest

/-- Apply the table constraints in written order. A table PRIMARY KEY with one
column of declared type INTEGER is a rowid alias, whatever its sort order. -/
def addTableConstraints (tableName : Identifier) (table : CatalogTable) :
    List Syntax.TableConstraint → Except ExprError CatalogTable
  | [] => .ok table
  | .primaryKey names algorithm :: rest => do
    if !table.primaryKey.isEmpty then throw (.multiplePrimaryKeys tableName)
    let positions ← keyPositions table.columns names
    let alias := match positions with
      | [position] => if aliasesRowid (table.columns[position]?.bind (·.declaredType)) then some position else none
      | _ => none
    let keyed ← setPrimaryKey table positions alias table.primaryKeyDescending algorithm
    addTableConstraints tableName keyed rest
  | .unique names algorithm :: rest => do
    let positions ← keyPositions table.columns names
    let keyed ← addUniqueKey table positions algorithm
    addTableConstraints tableName keyed rest

/-- The exact statistics tables that ANALYZE creates, which a catalog description may contain. -/
def statisticsTable (name : Identifier) (columns : List Syntax.ColumnDefinition)
    (constraints : List Syntax.TableConstraint) : Bool :=
  let plain := fun (names : List Identifier) => columns == names.map fun column =>
    { name := column, declaredType := none, constraints := [] }
  constraints.isEmpty && (statisticsColumns name.folded).any plain

/-- A table as {lit}`WITHOUT ROWID` makes it (ADR 0014, D4; {lit}`convertToWithoutRowidTable`):
no rowid alias, and each primary-key column NOT NULL, with ABORT unless it declares its own
NOT NULL. -/
def CatalogTable.asWithoutRowid (table : CatalogTable) : CatalogTable :=
  let columns := table.columns.mapIdx fun position (column : CatalogColumn) =>
    if table.primaryKey.contains position then { column with notNull := true } else column
  { table with withoutRowid := true, rowidAlias := none, columns }

/-- Resolve CREATE TABLE. Path 1 is the column list and path 2 the table constraints. A
{lit}`WITHOUT ROWID` table ({name}`CatalogTable.asWithoutRowid`) without a primary key is
SQLite's {lit}`PRIMARY KEY missing on table %s`, after the errors of its definitions. -/
def resolveCreateTable (context : ResolveContext) (catalog : Catalog) (index : Nat)
    (name : Identifier) (columns : List Syntax.ColumnDefinition)
    (constraints : List Syntax.TableConstraint) (options : Syntax.TableOptions := {}) : StatementResolution :=
  let statistics := context.mode == .description && statisticsTable name columns constraints
  if reservedName name && !statistics then
    if context.mode == .description then restrict index [0] .engineTable
    else prepareError catalog (.expression (.reservedName name))
  else match catalog.find name with
  | some (_, { entry := .table _, .. }) => prepareError catalog (.tableExists name)
  | some (_, { entry := .index _, .. }) => prepareError catalog (.indexNameUsed name)
  | none =>
    match addDefinitions context.profile.limits.columns name { columns := [] } columns >>=
        (addTableConstraints name · constraints) with
    | .error error => prepareError catalog (.expression error)
    | .ok table =>
      let table := if options.withoutRowid then table.asWithoutRowid else table
      if options.withoutRowid && table.primaryKey.isEmpty then
        prepareError catalog (.expression (.primaryKeyMissing name))
      else if columns.any (rowidName ·.name) then restrict index [1] .rowidColumnName
      else if context.mode == .execution && (!constraints.isEmpty || columns.any (!·.constraints.isEmpty)) then
        restrict index [1] .createTableConstraints
      else if columns.any (!·.constraints.all Syntax.ColumnConstraint.modeledDefault) then
        restrict index [1] .unmodeledDefault
      else .ok (.createTable catalog.length name table, catalog.createTable name table)

/-- Resolve CREATE INDEX, of a catalog description or in a script, in SQLite's order: the
table, its reserved name, the index name, the name in use, the key terms
({name}`indexKeys`, path 3) and the filter ({name}`indexFilter`, path 4), both over the
table alone and under the profile's {lit}`DQS_DDL`. A CREATE INDEX that runs builds the
index over the existing rows in execution. -/
def resolveCreateIndex (context : ResolveContext) (catalog : Catalog) (index : Nat)
    (name : Identifier) (unique : Bool) (tableName : Identifier) (terms : List Syntax.OrderTerm)
    (filter : Option Syntax.Expr) : StatementResolution :=
  match catalog.findTable tableName with
  | none => prepareError catalog (.noSuchTable tableName)
  | some (position, table) =>
    if reservedName tableName then prepareError catalog (.expression (.tableMayNotBeIndexed tableName))
    else if reservedName name then prepareError catalog (.expression (.reservedName name))
    else match catalog.find name with
    | some (_, { entry := .table _, .. }) => prepareError catalog (.tableNameUsed name)
    | some (_, { entry := .index _, .. }) => prepareError catalog (.indexExists name)
    | none =>
      let scope := Scope.single tableName table.columns !table.withoutRowid
      let dqs := context.profile.dqsDdl
      match indexKeys dqs scope table.columns terms with
      | .error issue => issueResolution catalog index [3] issue
      | .ok keys => match indexFilter dqs scope filter with
        | .error issue => issueResolution catalog index [4] issue
        | .ok resolvedFilter =>
          let created := { table := position, keys, unique, filter := resolvedFilter }
          .ok (.createIndex catalog.length name created, catalog.createIndex name created)

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
    | .primaryKey .. | .unique _ => some column)
    { name := definition.name, declaredType := reportedType definition.declaredType }

/-- Resolve ALTER TABLE ADD COLUMN. Path 1 is the column definition. -/
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
    else if definition.constraints.any Syntax.ColumnConstraint.isPrimaryKey && !table.primaryKey.isEmpty then
      prepareError catalog (.expression (.multiplePrimaryKeys tableName))
    else if definition.constraints.any Syntax.ColumnConstraint.nonconstantDefault then
      prepareError catalog (.expression (.defaultNotConstant definition.name))
    else if definition.constraints.any Syntax.ColumnConstraint.isPrimaryKey then prepareError catalog (.expression .cannotAddPrimaryKey)
    else if definition.constraints.any Syntax.ColumnConstraint.isUnique then prepareError catalog (.expression .cannotAddUnique)
    else if rowidName definition.name then restrict index [1] .rowidColumnName
    else
      match addedColumn definition with
      | none => restrict index [1] .addColumnConstraint
      | some column => .ok (.addColumn position column, catalog.addColumn position column)

end Belay.Sqlite
