import Belay.Sqlite.Resolution.SyntaxExpr
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

/-- One statement as written. For example, {lit}`COMMIT` is
{lean}`Statement.commit`. -/
inductive Statement where
  /-- {lit}`CREATE TABLE name (columns, constraints)`. -/
  | createTable (name : Identifier) (columns : List ColumnDefinition)
      (constraints : List TableConstraint)
  /-- {lit}`CREATE [UNIQUE] INDEX name ON table (terms) [WHERE filter]`: each key term is an
  expression with its sort order, and the filter is none for an index of every row. -/
  | createIndex (name : Identifier) (unique : Bool) (table : Identifier) (terms : List OrderTerm)
      (filter : Option Expr)
  /-- {lit}`ALTER TABLE table ADD COLUMN column`. -/
  | addColumn (table : Identifier) (column : ColumnDefinition)
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
  one. The {lit}`RETURNING` columns are {lit}`returning`, empty without the clause. -/
  | insert (table : Identifier) (columns : Option (List Identifier)) (rows : List (List Expr))
      (conflicts : List ConflictClause) (algorithm : Option ConflictAlgorithm := none)
      (returning : List ResultColumn := [])
  /-- {lit}`UPDATE table SET assignments [WHERE filter] [RETURNING columns]`. -/
  | update (table : Identifier) (assignments : List (Identifier × Expr)) (filter : Option Expr)
      (returning : List ResultColumn := [])
  /-- {lit}`DELETE FROM table [WHERE filter] [RETURNING columns]`. -/
  | delete (table : Identifier) (filter : Option Expr) (returning : List ResultColumn := [])
  /-- {lit}`SELECT columns FROM source joins [WHERE filter] [GROUP BY terms] [ORDER BY terms]
  [LIMIT limit [OFFSET offset]]`: the first table of {lit}`FROM` and the joins after it, in
  order; one table has no joins, and a {lit}`SELECT` without {lit}`FROM` has
  {lean}`(none : Option TableReference)` and no joins. An omitted clause is {lit}`none` or
  an empty list;
  {lit}`LIMIT offset, limit` gives both expressions. -/
  | select (columns : List ResultColumn) (source : Option TableReference) (joins : List Join) (filter : Option Expr)
      (groupBy : List Expr) (orderBy : List OrderTerm) (limit : Option Expr) (offset : Option Expr)
  deriving Repr, BEq

end Belay.Sqlite.Syntax
