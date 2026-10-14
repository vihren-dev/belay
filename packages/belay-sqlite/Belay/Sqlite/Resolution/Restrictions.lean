set_option doc.verso true

/-! The registry of model restrictions. A model restriction is SQL that SQLite accepts
but the model does not describe; resolution refuses it, and the user reads its
message. Each restriction is one constructor of {lit}`RestrictionKind`, which names the
decision that introduced it. Its stable id and its message are in
{lit}`Belay.Sqlite.RestrictionText`, and {lit}`docs/semantic-subset.md` lists every id. -/

namespace Belay.Sqlite

/-- A model restriction of name resolution. The comment of each constructor says what
the model does not describe and which decision introduced the restriction. -/
inductive RestrictionKind where
  /-- A schema contains only CREATE TABLE and CREATE INDEX statements (ADR 0008). -/
  | schemaStatement
  /-- Engine-managed tables other than sqlite_stat1 and sqlite_stat4 are not modeled (ADR 0008). -/
  | engineTable
  /-- Column names {lit}`rowid`, {lit}`_rowid_` and {lit}`oid` are not modeled (ADR 0008). -/
  | rowidColumnName
  /-- INTEGER PRIMARY KEY rowid aliases are not modeled (ADR 0008). -/
  | rowidAlias
  /-- Constraints and defaults in a CREATE TABLE that runs are not modeled (ADR 0008). -/
  | createTableConstraints
  /-- Only the {lit}`CURRENT_TIMESTAMP` default is modeled (ADR 0008). -/
  | unmodeledDefault
  /-- A CREATE INDEX that runs is not modeled (ADR 0008). -/
  | createIndexRuns
  /-- Only a nullable column without a default can be added (ADR 0008). -/
  | addColumnConstraint
  /-- Time values are not modeled (ADR 0008). -/
  | timeValue
  /-- Unique keys over TEXT or REAL columns are not modeled (ADR 0008). -/
  | keyAffinity
  /-- Only integer and NULL values are modeled in unique key columns (ADR 0008). -/
  | keyValue
  /-- A {lit}`SET` value that reads the row is not modeled for a column of a unique key
  (ADR 0012, amendment 1, owner decision on question 1). -/
  | rowDependentKey
  /-- A column named twice in INSERT is not modeled (ADR 0008). -/
  | insertColumnTwice
  /-- A column assigned twice in UPDATE is not modeled (ADR 0008). -/
  | updateColumnTwice
  /-- A rowid in RETURNING is not modeled (ADR 0012 slice 3a). -/
  | rowidInReturning
  /-- Queries of SQLite's own tables, such as {lit}`sqlite_schema`, are not modeled (ADR 0012 slice 1). -/
  | systemTable
  /-- Only {lit}`COUNT(*)`, {lit}`COUNT`, {lit}`MIN`, {lit}`MAX`, {lit}`SUM` and {lit}`AVG` of one argument, and {lit}`COALESCE` of two or more arguments are modeled as functions (ADR 0012 slices 1 and 2). -/
  | unmodeledFunction
  /-- An aggregate inside an expression is not modeled (ADR 0012 slice 1). -/
  | aggregateInExpression
  /-- A result column alias inside WHERE or an ORDER BY expression is not modeled (ADR 0012 slice 1). -/
  | aliasInExpression
  /-- A value used as a condition is not modeled (ADR 0012 slice 1). -/
  | valueAsCondition
  /-- A comparison of columns with different kinds of affinity is not modeled (ADR 0012 slice 1). -/
  | mixedAffinityComparison
  /-- A text value compared with a numeric column would be converted to a number (ADR 0012 slice 1). -/
  | textToNumber
  /-- A number compared with a TEXT column would be converted to text (ADR 0012 slice 1). -/
  | numberToText
  /-- Only a column name or a result column number is modeled in GROUP BY (ADR 0012 slice 1). -/
  | groupByTerm
  /-- A result column outside GROUP BY in an aggregate query is not modeled (ADR 0012 slice 1). -/
  | bareColumn
  /-- An aggregate query is modeled with ORDER BY result column numbers or aliases only (ADR 0012 slice 1). -/
  | aggregateOrderBy
  /-- Only an integer literal is modeled as LIMIT or OFFSET (ADR 0012 slice 1). -/
  | windowValue
  /-- A negative OFFSET is not modeled (ADR 0012 slice 1). -/
  | negativeOffset
  /-- SUM in a grouped query with LIMIT or OFFSET is not modeled, because SQLite may stop before an overflowing group (ADR 0012 slice 2). -/
  | windowedGroupSum
  deriving Repr, DecidableEq

end Belay.Sqlite
