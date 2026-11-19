import Belay.Sqlite.Tooling.Counterexamples.ReplayTriggerSql
import Belay.Sqlite.Tooling.Counterexamples.ReplayResolvedExpr
import Belay.Sqlite.Model.Queries.Preparation.ForeignKeyAction

set_option doc.verso true

namespace Belay.Sqlite.Replay
open Belay.Sqlite.Model

/-- The conflict clause of a table or column constraint. -/
private def conflictClause (algorithm : Option ConflictAlgorithm) : String :=
  (algorithm.map ((" ON CONFLICT " ++ ·) ∘ conflictSql)).getD ""

/-- The local column names for a table-level constraint. Their spelling matters to later DROP COLUMN.
Use an alternative ASCII spelling when the original table recorded a non-exact name. -/
private def positionsSql (table : CatalogTable) (positions : List Nat) : Option String := do
  let names ← positions.mapM fun index => do
    let name := (← table.columns[index]?).name
    if table.exactNames then pure name else
      pure (Identifier.ofString (if name.text.toUpper != name.text then name.text.toUpper else name.text.toLower))
  columnListSql names

/-- The REFERENCES part shared by column and table foreign keys. -/
private def referencesSql (key : ForeignKey) : Option String := do
  let columns ← if key.referenced.isEmpty then pure "" else columnListSql key.referenced
  return "REFERENCES " ++ (← identifier key.table) ++ columns ++ " ON DELETE " ++ key.onDelete.sqlName ++
    " ON UPDATE " ++ key.onUpdate.sqlName ++ (if key.deferred then " DEFERRABLE INITIALLY DEFERRED" else "")

/-- An unnamed CHECK retains its expression text and token spans. A named CHECK retains its
name and resolved expression. Both determine the label SQLite reports on failure. -/
private def checkSql (table : CatalogTable) (check : CheckConstraint) : Option String := do
  match check.source with
  | some source => return "CHECK (" ++ source.text ++ ")"
  | none => return "CONSTRAINT " ++ (← identifier (Identifier.ofString check.label)) ++
      " CHECK (" ++ (← resolvedExprSql table check.condition) ++ ")"

/-- The UNIQUE algorithm at a key position, or none for an omitted ON CONFLICT. -/
private def uniqueAlgorithm (table : CatalogTable) (idx : Nat) : Option ConflictAlgorithm :=
  table.uniqueAlgorithms[idx]?.join

/-- Render a column, including the key constraints that must be declared inline to reproduce
SQLite's descending primary keys and the catalog's inline UNIQUE positions. -/
private def columnSql (table : CatalogTable) (column : CatalogColumn) (index : Nat) : Option String := do
  let declared ← column.declaredType.mapM (identifier ∘ Identifier.ofString)
  let mut parts := [← identifier column.name] ++ declared.toList
  if column.notNull then
    parts := parts ++ ["NOT NULL" ++ conflictClause (if column.notNullAlgorithm == .abort then none else some column.notNullAlgorithm)]
  if table.primaryKeyDescending && table.primaryKey == [index] then
    parts := parts ++ ["PRIMARY KEY DESC" ++ conflictClause table.primaryKeyAlgorithm]
  if table.inlineUnique.contains index then
    let algorithm := (table.uniqueKeys.idxOf? [index]).bind (uniqueAlgorithm table)
    parts := parts ++ ["UNIQUE" ++ conflictClause algorithm]
  if let some d := column.defaultValue then parts := parts ++ ["DEFAULT " ++ d.sourceText]
  parts := parts ++ ["COLLATE " ++ column.collation.sqlName] ++ (← column.checks.mapM (checkSql table)) ++
    (← column.foreignKeys.mapM referencesSql)
  if let some gen := column.generated then
    parts := parts ++ ["AS (" ++ (← resolvedExprSql table gen.expression) ++ ") " ++
      (if gen.stored then "STORED" else "VIRTUAL")]
  return String.intercalate " " parts

/-- Propose a CREATE TABLE statement with the catalog's column constraints, key order,
foreign keys, STRICT and WITHOUT ROWID options. -/
def tableSql (name : Identifier) (table : CatalogTable) : Option String := do
  let mut definitions ← table.columns.zipIdx.mapM fun (column, index) => columnSql table column index
  let primary ← if table.primaryKey.isEmpty || table.primaryKeyDescending then pure [] else
    pure ["PRIMARY KEY " ++ (← positionsSql table table.primaryKey) ++ conflictClause table.primaryKeyAlgorithm]
  let mut before := []
  let mut afterKeys := []
  for (key, index) in table.uniqueKeys.zipIdx do
    if !(key.length == 1 && key.head?.any table.inlineUnique.contains) then
      let term := "UNIQUE " ++ (← positionsSql table key) ++ conflictClause (uniqueAlgorithm table index)
      if index < table.uniqueBeforePrimary then before := term :: before else afterKeys := term :: afterKeys
  definitions := definitions ++ before.reverse ++ primary ++ afterKeys.reverse ++ (← table.checks.mapM (checkSql table))
  for key in table.foreignKeys do
    definitions := definitions ++ ["FOREIGN KEY " ++ (← positionsSql table key.columns) ++ " " ++ (← referencesSql key)]
  let options := (if table.withoutRowid then ["WITHOUT ROWID"] else []) ++ (if table.strict then ["STRICT"] else [])
  let quoted ← identifier name
  let create := "CREATE TABLE " ++ quoted ++ " (" ++ String.intercalate ", " definitions ++ ")" ++
    (if options.isEmpty then "" else " " ++ String.intercalate ", " options) ++ ";\n"
  if table.quotedRename then
    let column ← identifier (← table.columns.head?).name
    return create ++ "ALTER TABLE " ++ quoted ++ " RENAME COLUMN " ++ column ++ " TO " ++ column ++ ";\n"
  return create

/-- Propose a CREATE INDEX statement. Column positions of the key and WHERE expression
refer to the indexed table, even when other catalog objects precede it. -/
def indexSql (catalog : Catalog) (name : Identifier) (index : CatalogIndex) : Option String := do
  let entry ← catalog[index.table]?
  let .table owner := entry.entry | none
  let table := { owner with exactNames := index.exactNames }
  let keys ← index.keys.mapM fun key => do
    let term ← match key.term with
      | .column position => columnReferenceSql table position
      | .expression expr => resolvedExprSql table expr
    return term ++ " COLLATE " ++ key.collation.sqlName ++ (if key.descending then " DESC" else "")
  let filter ← index.filter.mapM (resolvedExprSql table)
  return (if index.unique then "CREATE UNIQUE INDEX " else "CREATE INDEX ") ++ (← identifier name) ++
    " ON " ++ (← identifier entry.name) ++ " (" ++ String.intercalate ", " keys ++ ")" ++
    (filter.map (" WHERE " ++ ·)).getD "" ++ ";\n"

end Belay.Sqlite.Replay
