import Belay.Sqlite.Model.Resolution.Definitions

set_option doc.verso true

/-! Name resolution of ALTER TABLE ADD COLUMN. The prepare checks follow the order of
SQLite 3.51.0's {lit}`sqlite3AlterBeginAddColumn`, {lit}`sqlite3AddColumn`, the constraint
actions and {lit}`sqlite3AlterFinishAddColumn`, because SQLite reports the first error it
finds. Model restrictions follow the prepare checks. -/

namespace Belay.Sqlite.Model

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
    | .primaryKey .. | .unique _ | .check .. | .references .. | .generated .. | .deferral _ => some column)
    (definedColumn strict definition)

/-- The model restriction of an added column that SQLite checks only while ADD COLUMN runs, or
none: a generated column is {name}`RestrictionKind.addColumnGenerated`, a deferral clause
before the column's first {lit}`REFERENCES` is {name}`RestrictionKind.addColumnConstraint`,
because SQLite applies it to a key of another column, and a column of a
{lit}`STRICT` table without a type that it admits ({name}`StrictType.ofReported`) is
{name}`RestrictionKind.addColumnStrictType`, as is a default that does not fit the type
({lit}`strictDefaultFits`, after the column is built). -/
def addColumnRestriction (table : CatalogTable) (definition : Syntax.ColumnDefinition) : Option RestrictionKind :=
  if definition.constraints.any (· matches .generated ..) then some .addColumnGenerated
  else if (definition.constraints.takeWhile (!· matches .references ..)).any (· matches .deferral _) then
    some .addColumnConstraint
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

/-- Whether an expression is the keyword {lit}`NULL`. It lists every constructor, so a new
expression form needs a decision here. -/
def isNullKeyword : Syntax.Expr → Bool
  | .null => true
  | .numeric _ | .string _ | .blob _ | .parameter _ | .currentTime _ | .identifier .. | .qualified ..
  | .negate _ | .positive _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _
  | .call .. | .arithmetic .. | .cast .. | .collate .. | .exists _ | .inQuery .. | .subquery _
  | .inList .. | .between .. | .caseOf .. | .concatenate .. | .raise .. => false

/-- Whether SQLite treats the written default of an added column as no default for the
{lit}`REFERENCES` check of {lit}`sqlite3AlterFinishAddColumn`: no DEFAULT is written, or the
last written DEFAULT (each replaces the preceding one) is the literal {lit}`NULL`, also with
the unary plus that the grammar admits before a bare term ({lit}`DEFAULT +NULL`). The check reads
this syntax, not the value: {lit}`-NULL`, a cast or any other expression that evaluates to NULL
is a non-NULL default. Parenthesized defaults other than a parameter are not translated, so
{lit}`DEFAULT (NULL)` and {lit}`DEFAULT (+NULL)` never reach this function. The model has no column
default value for a signed NULL, so a signed NULL default is unsupported anyway; the unary plus
case only keeps this function equal to SQLite's rule. For example, the column
{lit}`c DEFAULT NULL` gives
{lean}`literalNullDefault { name := Identifier.ofString "c", declaredType := none, constraints := [.default .null "NULL"] }`. -/
def literalNullDefault (definition : Syntax.ColumnDefinition) : Bool :=
  let written : Option Syntax.Expr := definition.constraints.reverse.findSome? fun constraint =>
    match constraint with
    | .default expression _ => some expression
    | .notNull _ | .primaryKey .. | .unique _ | .collate _ | .check .. | .references .. | .generated .. | .deferral _ => none
  match written with
  | none | some .null => true
  | some (.positive operand) => isNullKeyword operand
  | some (.numeric _) | some (.string _) | some (.blob _) | some (.parameter _) | some (.currentTime _)
  | some (.identifier ..) | some (.qualified ..) | some (.negate _) | some (.compare ..) | some (.and ..)
  | some (.or ..) | some (.not _) | some (.isNull ..) | some (.callStar _) | some (.call ..)
  | some (.arithmetic ..) | some (.cast ..) | some (.collate ..) | some (.exists _) | some (.inQuery ..)
  | some (.subquery _) | some (.inList ..) | some (.between ..) | some (.caseOf ..)
  | some (.concatenate ..) | some (.raise ..) => false

/-- The foreign keys of a column added at the position, from its constraints in written order:
each {lit}`REFERENCES` adds one, and a deferral clause sets whether the last of them so far is
deferred. -/
def addedForeignKeys (position : Nat) (constraints : List Syntax.ColumnConstraint) : List ForeignKey :=
  constraints.foldl (fun keys constraint => match constraint with
    | .references target columns onDelete onUpdate =>
      keys ++ [{ table := target, columns := [position], referenced := columns, onDelete, onUpdate }]
    | .deferral deferred => updateLast keys fun key => { key with deferred }
    | .notNull _ | .primaryKey .. | .unique _ | .default .. | .collate _ | .check .. | .generated .. => keys) []

/-- Resolve ALTER TABLE ADD COLUMN. Path 1 is the column definition. Its CHECK constraints
resolve over the table with the new column ({name}`columnChecks`); one that SQLite cannot
resolve is {name}`RestrictionKind.addColumnCheckError`, as SQLite reports it while the
statement runs. A default that does not fit the column's strict type
({name}`strictDefaultFits`) is {name}`RestrictionKind.addColumnStrictType`. Its
{lit}`REFERENCES` constraints are its foreign keys, and a deferral clause sets whether the last
of them so far is deferred. -/
def resolveAddColumn (context : ResolveContext) (catalog : Catalog) (enforced : Bool)
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
    else if rowidName definition.name then restrict [1] .rowidColumnName
    else match addColumnRestriction table definition with
    | some kind => restrict [1] kind
    | none =>
      match addedColumn table.strict definition with
      | none => restrict [1] .addColumnConstraint
      | some column =>
        if !strictDefaultFits column then restrict [1] .addColumnStrictType else
        let scope := Scope.single tableName (table.columns ++ [column]) !table.withoutRowid
        match columnChecks context.profile.dqsDdl scope definition with
        | .error (.prepare _) => restrict [1] .addColumnCheckError
        | .error (.restriction path reason) => restrict (1 :: path) reason
        | .ok checks =>
          let column := { column with checks, foreignKeys := addedForeignKeys table.columns.length definition.constraints }
          .ok (.addColumn position column (enforced && !column.foreignKeys.isEmpty && !literalNullDefault definition),
            catalog.addColumn position column)

end Belay.Sqlite.Model
