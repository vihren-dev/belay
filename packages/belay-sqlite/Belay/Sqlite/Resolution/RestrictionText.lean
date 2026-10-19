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
  | .unmodeledDefault => "unmodeled-default"
  | .indexStringTerm => "index-string-term"
  | .indexDateFunction => "index-date-function"
  | .indexJsonFunction => "index-json-function"
  | .unknownCollation => "unknown-collation"
  | .checkFunction => "check-function"
  | .addColumnCheckError => "add-column-check-error"
  | .generatedFunction => "generated-function"
  | .generatedLoop => "generated-loop"
  | .upsertGenerated => "upsert-generated"
  | .addColumnGenerated => "add-column-generated"
  | .addColumnConstraint => "add-column-constraint"
  | .rowDependentKey => "row-dependent-key"
  | .conflictWithoutTarget => "conflict-without-target"
  | .mixedConflictAlgorithms => "mixed-conflict-algorithms"
  | .constraintAlgorithmUpdate => "constraint-algorithm-update"
  | .replaceDefault => "replace-default"
  | .insertColumnTwice => "insert-column-twice"
  | .updateColumnTwice => "update-column-twice"
  | .rowidName => "rowid-name"
  | .joinOperator => "join-operator"
  | .laterTableInOn => "later-table-in-on"
  | .systemTable => "system-table"
  | .unmodeledFunction => "unmodeled-function"
  | .aggregateInExpression => "aggregate-in-expression"
  | .aliasInExpression => "alias-in-expression"
  | .groupByTerm => "group-by-term"
  | .bareColumn => "bare-column"
  | .aggregateOrderBy => "aggregate-order-by"
  | .windowValue => "window-value"
  | .negativeOffset => "negative-offset"
  | .windowedGroupSum => "windowed-group-sum"
  | .constantFunctionError => "constant-function-error"
  | .tableFunction => "table-function"
  | .functionJoin => "function-join"
  | .laterSourceInArguments => "later-source-in-arguments"

/-- The message of a restriction that users read: what the model does not describe,
and what to write instead. -/
def RestrictionKind.message : RestrictionKind → String
  | .schemaStatement => "a schema contains only CREATE TABLE and CREATE INDEX statements; move the other statement to the script"
  | .engineTable => "engine-managed tables other than sqlite_stat1 and sqlite_stat4 are not modeled; remove the table from the schema"
  | .rowidColumnName => "column names rowid, _rowid_ and oid are not modeled; rename the column"
  | .unmodeledDefault => "default expression is not modeled; use a literal default"
  | .indexStringTerm => "a string literal as an index key is not modeled; name the column without quotes"
  | .indexDateFunction => "a date and time function in an index key or WHERE clause is not modeled; index the column instead"
  | .indexJsonFunction => "a JSON function in an index key or WHERE clause is not modeled; index the column instead"
  | .unknownCollation => "COLLATE with a name other than BINARY, NOCASE or RTRIM in an expression is not modeled; use one of these collations"
  | .checkFunction => "a time keyword, a date and time function or a JSON function in a CHECK constraint is not modeled; check the column values instead"
  | .addColumnCheckError => "a CHECK of ADD COLUMN that names no column of the table, or uses an aggregate, is not modeled; correct the CHECK"
  | .generatedFunction => "a date and time function or a JSON function in a generated column is not modeled; compute the value in the write"
  | .generatedLoop => "generated columns that read each other in a loop are not modeled; SQLite refuses the table"
  | .upsertGenerated => "DO UPDATE of a generated column is not modeled; assign the columns that it reads"
  | .addColumnGenerated => "ADD COLUMN of a generated column is not modeled; create the table with it"
  | .addColumnConstraint => "the default of the added column is not modeled; use a literal default or no default"
  | .rowDependentKey => "a SET value that reads the row is not modeled for a column of a unique key; assign a constant value"
  | .conflictWithoutTarget => "DO UPDATE without a conflict target is not modeled for a table with more than one key; name the target columns"
  | .mixedConflictAlgorithms => "keys with different conflict algorithms other than REPLACE are not modeled; use one algorithm, for example with INSERT OR"
  | .constraintAlgorithmUpdate => "UPDATE of a table with ON CONFLICT constraint algorithms is not modeled; remove the algorithms or use INSERT"
  | .replaceDefault => "REPLACE of a NOT NULL column with a default is not modeled; write the value instead of NULL"
  | .insertColumnTwice => "a column named twice in INSERT is not modeled; name each column once"
  | .updateColumnTwice => "a column assigned twice in UPDATE is not modeled; assign each column once"
  | .rowidName => "the rowid names rowid, _rowid_ and oid are not modeled in expressions over a table; name the table's columns"
  | .joinOperator => "this join operator is refused by SQLite and not modeled; write JOIN, LEFT JOIN or a comma"
  | .laterTableInOn => "an ON condition that names a table joined after it is not modeled; move the condition to WHERE or to the later join"
  | .systemTable => "queries of SQLite's own tables, such as sqlite_schema, are not modeled; query an application table"
  | .unmodeledFunction => "only COUNT(*), COUNT, MIN, MAX, SUM and AVG of one argument, COALESCE of two or more arguments, json_extract, ->, ->>, json_type, json_valid, json_array_length and json are modeled as functions"
  | .aggregateInExpression => "an aggregate inside an expression is not modeled; use the aggregate as a whole result column"
  | .aliasInExpression => "a result column alias inside WHERE or an ORDER BY expression is not modeled; write the column expression"
  | .groupByTerm => "only a column name or a result column number is modeled in GROUP BY"
  | .bareColumn => "a result column outside GROUP BY in an aggregate query is not modeled; group by it or aggregate it"
  | .aggregateOrderBy => "an aggregate query is modeled with ORDER BY result column numbers or aliases only"
  | .windowValue => "only an integer literal is modeled as LIMIT or OFFSET; write an integer"
  | .negativeOffset => "a negative OFFSET is not modeled; write OFFSET 0 or more"
  | .windowedGroupSum => "SUM in a grouped query with LIMIT or OFFSET is not modeled, because SQLite may stop before an overflowing group; remove the window or the SUM"
  | .constantFunctionError => "a constant value in VALUES or SET whose JSON function fails is not modeled; correct the JSON text or the path"
  | .tableFunction => "only json_each with one or two arguments is modeled as a table-valued function in FROM; use json_each or a table"
  | .functionJoin => "json_each as the right operand of RIGHT or FULL JOIN, with NATURAL or USING, or before a NATURAL JOIN, is not modeled; write JOIN or LEFT JOIN with ON"
  | .laterSourceInArguments => "an argument of json_each that reads a later source is not modeled; write the source before json_each"

/-- Every restriction, in the order of the registry. -/
def RestrictionKind.all : List RestrictionKind :=
  [.schemaStatement, .engineTable, .rowidColumnName, .unmodeledDefault, .indexStringTerm, .indexDateFunction, .indexJsonFunction, .unknownCollation, .checkFunction, .addColumnCheckError, .generatedFunction, .generatedLoop, .upsertGenerated, .addColumnGenerated, .addColumnConstraint, .rowDependentKey, .conflictWithoutTarget, .mixedConflictAlgorithms, .constraintAlgorithmUpdate, .replaceDefault, .insertColumnTwice, .updateColumnTwice, .rowidName, .joinOperator, .laterTableInOn, .systemTable, .unmodeledFunction, .aggregateInExpression, .aliasInExpression, .groupByTerm, .bareColumn, .aggregateOrderBy, .windowValue, .negativeOffset, .windowedGroupSum, .constantFunctionError, .tableFunction, .functionJoin, .laterSourceInArguments]

/-- For every restriction, it is in {name}`RestrictionKind.all`. Proof sketch: case
analysis on the restriction. -/
theorem RestrictionKind.mem_all (kind : RestrictionKind) : kind ∈ RestrictionKind.all := by
  cases kind <;> simp [RestrictionKind.all]

-- The ids are distinct.
#guard (RestrictionKind.all.map RestrictionKind.id).eraseDups.length == RestrictionKind.all.length

end Belay.Sqlite
