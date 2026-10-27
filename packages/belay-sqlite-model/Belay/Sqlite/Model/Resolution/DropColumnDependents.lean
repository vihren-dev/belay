import Belay.Sqlite.Model.Resolution.ColumnDropCatalog
import Belay.Sqlite.Model.Resolution.ColumnDropSpec
import Belay.Sqlite.Model.Resolution.RenameCatalog

set_option doc.verso true

/-! The objects that make SQLite refuse ALTER TABLE DROP COLUMN after it edited the table text (ADR 0019,
D4). SQLite parses every stored definition again with the column gone ({lit}`renameTestSchema` with the words
{lit}`after drop column`) and reports the first definition that fails, in schema order. A table fails when a key,
a CHECK constraint, a generated expression or a foreign key still names the column; an index fails when it reads
it; a view or a trigger fails when its text no longer resolves. The message prints the name as the text spells it,
so the model gives an error only where it knows the spelling, and restricts the statement otherwise. -/

namespace Belay.Sqlite.Model

/-- What a table still holds that names a column that leaves it. -/
inductive TableDependency where
  /-- A table-level UNIQUE key. -/
  | keys
  /-- A CHECK constraint of another column or of the table. -/
  | checks
  /-- A generated column. -/
  | generated
  /-- A foreign key of another column or of the table. -/
  | foreign
  /-- No column that stays is a non-generated column. -/
  | onlyGenerated
  deriving Repr, DecidableEq

/-- Whether a generated expression of a column other than the one at {lit}`index` reads that column. -/
def CatalogTable.generatedReads (index : Nat) (table : CatalogTable) : Bool :=
  (table.columns.eraseIdx index).any fun column =>
    (column.generated.map (·.expression.readsColumn index)).getD false

/-- Whether a foreign key that stays names the column at {lit}`index` in its child columns. -/
def CatalogTable.foreignNames (index : Nat) (table : CatalogTable) : Bool :=
  (table.columns.eraseIdx index).any (fun column => column.foreignKeys.any (·.columns.contains index)) ||
    table.foreignKeys.any (·.columns.contains index)

/-- Whether every column that stays when the column at {lit}`index` leaves is a generated column. -/
def CatalogTable.leavesOnlyGenerated (index : Nat) (table : CatalogTable) : Bool :=
  (table.columns.eraseIdx index).all (·.generated.isSome)

/-- The kinds of failure of the table after the drop of the column at {lit}`index`, each once: the kinds of
definition that name the column, none of those that go with the column, and a table that would keep only generated
columns. -/
def CatalogTable.dependencies (index : Nat) (table : CatalogTable) : List TableDependency :=
  (if table.uniqueKeys.any (·.contains index) then [.keys] else []) ++
    (if (table.checksAfterDrop index).any (·.condition.readsColumn index) then [.checks] else []) ++
    (if table.generatedReads index then [.generated] else []) ++
    (if table.foreignNames index then [.foreign] else []) ++
    (if table.leavesOnlyGenerated index then [.onlyGenerated] else [])

/-- The written spelling of the first name in the text of a CHECK constraint that is the column at
{lit}`index`: none when the text has no such name, writes it with a quote, or qualifies a name with the table, because
the error of SQLite then prints more than the name. -/
def CheckText.writtenColumn? (index : Nat) (text : CheckText) : Option Identifier :=
  if text.names.any (·.target == .table) then none
  else match text.names.find? (·.target == .column index) with
    | some name =>
      if name.quote == .none then
        (String.fromUTF8? (text.text.toUTF8.extract name.start name.stop)).map Identifier.ofString
      else none
    | none => none

/-- The error of the table for the one kind of definition that names the column, or the restriction when the model
does not know the spelling of that definition. {lit}`declared` is the column as the table declares it. -/
def CatalogTable.dependencyFailure (index : Nat) (declared name : Identifier) (table : CatalogTable) :
    TableDependency → RenameFailure
  | .checks =>
    match ((table.checksAfterDrop index).find? (·.condition.readsColumn index)).bind (·.source) with
    | some text => match text.writtenColumn? index with
      | some written => .prepare (.dependentObject .table name .afterDropColumn (.expression (.noSuchColumn written)))
      | none => .restricted .alterDrop
    | none => .restricted .alterDrop
  | .keys | .generated =>
    if table.exactNames && !table.quotedRename then
      .prepare (.dependentObject .table name .afterDropColumn (.expression (.noSuchColumn declared)))
    else .restricted .alterDrop
  | .foreign =>
    if table.exactNames && !table.quotedRename then
      .prepare (.dependentObject .table name .afterDropColumn (.expression (.unknownForeignKeyColumn declared)))
    else .restricted .alterDrop
  | .onlyGenerated => .prepare (.dependentObject .table name .afterDropColumn (.expression .onlyGeneratedColumns))

/-- The failure of the table itself after the drop: none when nothing names the column, the error of the kind when
one kind of definition does, and a restriction when several kinds do, because SQLite then reports the first that
it parses and the model does not order them. -/
def CatalogTable.dropFailure? (index : Nat) (declared name : Identifier) (table : CatalogTable) :
    Option RenameFailure :=
  match table.dependencies index with
  | [] => none
  | [kind] => some (table.dependencyFailure index declared name kind)
  | _ :: _ :: _ => some (.restricted .alterDrop)

/-- Whether a trigger of the table at the catalog position names the column in the column list of
{lit}`UPDATE OF`. SQLite keeps such a name, which no column has, and the model does not describe a later column
of that name. -/
def CatalogTrigger.updatesColumn (declared tableName : Identifier) (trigger : CatalogTrigger) : Bool :=
  trigger.table.sameName tableName && match trigger.event with
    | .update names => names.any (·.sameName declared)
    | .insert | .delete => false

end Belay.Sqlite.Model
