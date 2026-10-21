import Belay.Sqlite.Resolution.SyntaxDefinitions
import Belay.Sqlite.Resolution.ConflictAlgorithm

set_option doc.verso true

/-! Statements as written, before name resolution, over the expressions and clauses of
{lit}`SyntaxExpr`. Names are the decoded identifier text, with their case kept; omitted
parts are {lit}`none`. -/

namespace Belay.Sqlite.Syntax

/-- What an {lit}`ON CONFLICT` clause of INSERT does with a row that conflicts. -/
inductive ConflictAction where
  /-- {lit}`DO NOTHING`: skip the row. -/
  | nothing
  /-- {lit}`DO UPDATE SET assignments [WHERE filter]`: update the existing row. -/
  | update (assignments : List (Identifier × Expr)) (filter : Option Expr)
  deriving Repr, BEq

/-- One {lit}`ON CONFLICT [(target)] action` clause of INSERT. The target is a list of
column names as written, or {lean}`(none : Option (List Identifier))` for a clause without
target. -/
structure ConflictClause where
  /-- The target column names, or none. -/
  target : Option (List Identifier)
  /-- The action. -/
  action : ConflictAction
  deriving Repr, BEq

/-- The table options of CREATE TABLE ({lit}`table_option_set`). Use {lean}`({} : TableOptions)`
for a table without options. -/
structure TableOptions where
  /-- {lit}`WITHOUT ROWID`. -/
  withoutRowid : Bool := false
  /-- {lit}`STRICT` (ADR 0014, slice 6). -/
  strict : Bool := false
  deriving Repr, BEq

/-- One statement as written. For example, {lit}`COMMIT` is
{lean}`Statement.commit`. -/
inductive Statement where
  /-- {lit}`CREATE TABLE name (columns, constraints) options`. -/
  | createTable (name : Identifier) (columns : List ColumnDefinition)
      (constraints : List TableConstraint) (options : TableOptions := {})
  /-- {lit}`CREATE [UNIQUE] INDEX name ON table (terms) [WHERE filter]`: each key term is an
  expression with its sort order, and the filter is none for an index of every row. -/
  | createIndex (name : Identifier) (unique : Bool) (table : Identifier) (terms : List OrderTerm)
      (filter : Option Expr)
  /-- {lit}`ALTER TABLE table ADD COLUMN column`. -/
  | addColumn (table : Identifier) (column : ColumnDefinition)
  /-- {lit}`DROP TABLE [IF EXISTS] name` (ADR 0014, slice 7); {lit}`ifExists` is true with
  {lit}`IF EXISTS`. -/
  | dropTable (name : Identifier) (ifExists : Bool)
  /-- {lit}`DROP INDEX [IF EXISTS] name` (ADR 0014, slice 7); {lit}`ifExists` is true with
  {lit}`IF EXISTS`. -/
  | dropIndex (name : Identifier) (ifExists : Bool)
  /-- {lit}`BEGIN`. -/
  | begin
  /-- {lit}`COMMIT` or {lit}`END`. -/
  | commit
  /-- {lit}`ROLLBACK`. -/
  | rollback
  /-- {lit}`INSERT INTO table [(columns)] VALUES rows` and its {lit}`ON CONFLICT`
  clauses in written order; a missing column list is
  {lean}`(none : Option (List Identifier))`, and an INSERT without clauses has
  {lean}`([] : List ConflictClause)`. The algorithm of {lit}`INSERT OR algorithm` or of
  {lit}`REPLACE INTO` is {lit}`algorithm`, {lean}`(none : Option ConflictAlgorithm)` without
  one. The {lit}`RETURNING` columns are {lit}`returning`, empty without the clause. The
  subqueries of the statement are {lit}`subqueries`, as for {lit}`SELECT`. -/
  | insert (table : Identifier) (columns : Option (List Identifier)) (rows : List (List Expr))
      (conflicts : List ConflictClause) (algorithm : Option ConflictAlgorithm := none)
      (returning : List ResultColumn := []) (subqueries : List Subquery := [])
  /-- {lit}`UPDATE table SET assignments [WHERE filter] [RETURNING columns]`, with the
  subqueries of the statement, as for {lit}`SELECT`. -/
  | update (table : Identifier) (assignments : List (Identifier × Expr)) (filter : Option Expr)
      (returning : List ResultColumn := []) (subqueries : List Subquery := [])
  /-- {lit}`DELETE FROM table [WHERE filter] [RETURNING columns]`, with the subqueries of the
  statement, as for {lit}`SELECT`. -/
  | delete (table : Identifier) (filter : Option Expr) (returning : List ResultColumn := [])
      (subqueries : List Subquery := [])
  /-- {lit}`SELECT columns FROM source joins [WHERE filter] [GROUP BY terms] [ORDER BY terms]
  [LIMIT limit [OFFSET offset]]`: the first table of {lit}`FROM` and the joins after it, in
  order; one table has no joins, and a {lit}`SELECT` without {lit}`FROM` has
  {lean}`(none : Option TableReference)` and no joins. An omitted clause is {lit}`none` or
  an empty list;
  {lit}`LIMIT offset, limit` gives both expressions. The subqueries of the statement are
  {lit}`subqueries`, in the order of their text ({name}`Subquery`); empty without one. The
  {lit}`HAVING` condition is {lit}`having` and {lit}`SELECT DISTINCT` has {lit}`distinct`
  (ADR 0018, D3). -/
  | select (columns : List ResultColumn) (source : Option TableReference) (joins : List Join) (filter : Option Expr)
      (groupBy : List Expr) (orderBy : List OrderTerm) (limit : Option Expr) (offset : Option Expr)
      (subqueries : List Subquery := []) (having : Option Expr := none) (distinct : Bool := false)
  deriving Repr, BEq

end Belay.Sqlite.Syntax
