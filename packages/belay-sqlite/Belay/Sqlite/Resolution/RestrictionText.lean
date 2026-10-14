import Belay.Sqlite.Resolution.Restrictions

set_option doc.verso true

/-! The stable ids and the messages of the model restrictions in
{name}`Belay.Sqlite.RestrictionKind`. An id names the restriction in reports and in
{lit}`docs/semantic-subset.md`; it does not change when the message changes. -/

namespace Belay.Sqlite

/-- The stable id of a restriction: lowercase words joined by hyphens. -/
def RestrictionKind.id : RestrictionKind → String
  | .schemaStatement => "schema-statement"
  | .engineTable => "engine-table"
  | .rowidColumnName => "rowid-column-name"
  | .rowidAlias => "rowid-alias"
  | .createTableConstraints => "create-table-constraints"
  | .unmodeledDefault => "unmodeled-default"
  | .createIndexRuns => "create-index-runs"
  | .addColumnConstraint => "add-column-constraint"
  | .timeValue => "time-value"
  | .keyAffinity => "key-affinity"
  | .keyValue => "key-value"
  | .columnInValue => "column-in-value"
  | .insertColumnTwice => "insert-column-twice"
  | .updateColumnTwice => "update-column-twice"
  | .literalComparison => "literal-comparison"
  | .nonIntegerFilter => "non-integer-filter"
  | .filterForm => "filter-form"
  | .rowidInReturning => "rowid-in-returning"
  | .returningTarget => "returning-target"
  | .systemTable => "system-table"
  | .unmodeledFunction => "unmodeled-function"
  | .aggregateInExpression => "aggregate-in-expression"
  | .aliasInExpression => "alias-in-expression"
  | .valueAsCondition => "value-as-condition"
  | .mixedAffinityComparison => "mixed-affinity-comparison"
  | .textToNumber => "text-to-number"
  | .numberToText => "number-to-text"
  | .groupByTerm => "group-by-term"
  | .bareColumn => "bare-column"
  | .aggregateOrderBy => "aggregate-order-by"
  | .windowValue => "window-value"
  | .negativeOffset => "negative-offset"
  | .windowedGroupSum => "windowed-group-sum"

/-- The message of a restriction that users read: what the model does not describe,
and what to write instead. -/
def RestrictionKind.message : RestrictionKind → String
  | .schemaStatement => "a schema contains only CREATE TABLE and CREATE INDEX statements; move the other statement to the script"
  | .engineTable => "engine-managed tables other than sqlite_stat1 and sqlite_stat4 are not modeled; remove the table from the schema"
  | .rowidColumnName => "column names rowid, _rowid_ and oid are not modeled; rename the column"
  | .rowidAlias => "INTEGER PRIMARY KEY rowid aliases are not modeled; declare the key column with another type, such as BIGINT"
  | .createTableConstraints => "constraints and defaults in a CREATE TABLE that runs are not modeled; create the table with plain columns"
  | .unmodeledDefault => "only the CURRENT_TIMESTAMP default is modeled; remove the other default"
  | .createIndexRuns => "a CREATE INDEX that runs is not modeled; remove the CREATE INDEX statement"
  | .addColumnConstraint => "only a nullable column without a default can be added"
  | .timeValue => "time values are not modeled; write the time as a text literal"
  | .keyAffinity => "unique keys over TEXT or REAL columns are not modeled; write only to tables whose key columns have INTEGER, NUMERIC or BLOB affinity"
  | .keyValue => "only integer and NULL values are modeled in unique key columns; write an integer or NULL key value"
  | .columnInValue => "column references in values are not modeled; write a value that names no column"
  | .insertColumnTwice => "a column named twice in INSERT is not modeled; name each column once"
  | .updateColumnTwice => "a column assigned twice in UPDATE is not modeled; assign each column once"
  | .literalComparison => "a comparison of two literals is not modeled; compare a column with a literal"
  | .nonIntegerFilter => "only an integer equality with an INTEGER, NUMERIC or BLOB column is modeled; compare such a column with an integer literal"
  | .filterForm => "only a column equality filter is modeled; write WHERE column = integer"
  | .rowidInReturning => "a rowid in RETURNING is not modeled; return the table's columns"
  | .returningTarget => "RETURNING is modeled only on INSERT and UPDATE; remove it"
  | .systemTable => "queries of SQLite's own tables, such as sqlite_schema, are not modeled; query an application table"
  | .unmodeledFunction => "only COUNT(*), COUNT, MIN, MAX, SUM and AVG of one argument, and COALESCE of two or more arguments are modeled as functions"
  | .aggregateInExpression => "an aggregate inside an expression is not modeled; use the aggregate as a whole result column"
  | .aliasInExpression => "a result column alias inside WHERE or an ORDER BY expression is not modeled; write the column expression"
  | .valueAsCondition => "a value used as a condition is not modeled; write a comparison"
  | .mixedAffinityComparison => "a comparison of columns with different kinds of affinity is not modeled; compare columns with the same kind"
  | .textToNumber => "a text value compared with a numeric column would be converted to a number; write a number"
  | .numberToText => "a number compared with a TEXT column would be converted to text; write a text value"
  | .groupByTerm => "only a column name or a result column number is modeled in GROUP BY"
  | .bareColumn => "a result column outside GROUP BY in an aggregate query is not modeled; group by it or aggregate it"
  | .aggregateOrderBy => "an aggregate query is modeled with ORDER BY result column numbers or aliases only"
  | .windowValue => "only an integer literal is modeled as LIMIT or OFFSET; write an integer"
  | .negativeOffset => "a negative OFFSET is not modeled; write OFFSET 0 or more"
  | .windowedGroupSum => "SUM in a grouped query with LIMIT or OFFSET is not modeled, because SQLite may stop before an overflowing group; remove the window or the SUM"

/-- Every restriction, in the order of the registry. -/
def RestrictionKind.all : List RestrictionKind :=
  [.schemaStatement, .engineTable, .rowidColumnName, .rowidAlias, .createTableConstraints, .unmodeledDefault, .createIndexRuns, .addColumnConstraint, .timeValue, .keyAffinity, .keyValue, .columnInValue, .insertColumnTwice, .updateColumnTwice, .literalComparison, .nonIntegerFilter, .filterForm, .rowidInReturning, .returningTarget, .systemTable, .unmodeledFunction, .aggregateInExpression, .aliasInExpression, .valueAsCondition, .mixedAffinityComparison, .textToNumber, .numberToText, .groupByTerm, .bareColumn, .aggregateOrderBy, .windowValue, .negativeOffset, .windowedGroupSum]

/-- For every restriction, it is in {name}`RestrictionKind.all`. Proof sketch: case
analysis on the restriction. -/
theorem RestrictionKind.mem_all (kind : RestrictionKind) : kind ∈ RestrictionKind.all := by
  cases kind <;> simp [RestrictionKind.all]

-- The ids are distinct.
#guard (RestrictionKind.all.map RestrictionKind.id).eraseDups.length == RestrictionKind.all.length

end Belay.Sqlite
