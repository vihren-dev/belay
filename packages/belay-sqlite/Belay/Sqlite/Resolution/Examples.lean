import Belay.Sqlite.Resolution.SchemaScript
import Belay.Sqlite.Resolution.Messages

set_option doc.verso true

/-! Examples of {name}`Belay.Sqlite.resolve`, checked by {lit}`#guard` in the compiled
evaluator when the package builds. They check this repository's resolution rules
for each statement, each prepare error, the limits under a lowered profile limit,
the affinity and rowid-alias rules, ASCII-only folding, the shared namespace and
the transactions. The conformance suite compares the same rules with SQLite. -/

namespace Belay.Sqlite.Resolution.Examples

open Belay.Sqlite Syntax

/-- SQLite 3.51.0 with its documented default limits. -/
def defaults : Profile := Profile.documented "3.51.0" "2025-11-04 19:38:17 fb2c931ae597f8d00a37574ff67aeed3eced4e5547f9120744ae4bfa8e74527b"

/-- The same release with the column limit lowered to 3, so a constant limit fails. -/
def lowered : Profile := { defaults with limits := { defaults.limits with columns := 3 } }

/-- Resolve statements that the execution semantics runs, from a catalog. -/
def migration (catalog : Catalog) (script : List Syntax.Statement) (profile : Profile := defaults) : ResolveResult :=
  resolve { profile, mode := .execution } catalog script

/-- Resolve a catalog description from the empty catalog. -/
def schema (script : List Syntax.Statement) : ResolveResult :=
  resolve { profile := defaults, mode := .description } [] script

/-- A column definition without constraints. -/
def column (name : Identifier) (declaredType : Option String := some "TEXT") : ColumnDefinition :=
  { name, declaredType, constraints := [] }

/-- The statements of a resolution, or the empty list for a restriction. -/
def statements : ResolveResult → List Resolved.Statement
  | .resolved statements _ => statements
  | .restricted _ => []

/-- The catalog after a resolution, or the empty catalog for a restriction. -/
def catalogOf : ResolveResult → Catalog
  | .resolved _ catalog => catalog
  | .restricted _ => []

/-- Whether the resolution is a model restriction. -/
def restricted : ResolveResult → Bool
  | .restricted _ => true
  | .resolved .. => false

/-- The reason of a model restriction, or the empty text for a resolution. -/
def reason : ResolveResult → String
  | .restricted restriction => restriction.reason
  | .resolved .. => ""

/-- A catalog with table {lit}`t(a TEXT, b INTEGER)`. -/
def tableT : Catalog := catalogOf (migration [] [.createTable (name! "t") [column (name! "a"), column (name! "b") (some "INTEGER")] []])

-- Affinity rules in documented order; "CHARINT" and "FLOATING POINT" contain INT.
#guard [some "CHARINT", some "FLOATING POINT", some "VARCHAR(10)", some "DOUBLE", none,
  some "real blob", some "DECIMAL"].map affinityOf == [.integer, .integer, .text, .real, .blob, .blob, .numeric]

-- Rowid alias (slice 5b): INTEGER PRIMARY KEY, as a column or a table constraint, is an
-- alias, and the schema runs; DESC and BIGINT are not aliases, and DESC makes the key
-- descending.
#guard (catalogOf (schema [.createTable (name! "t") [{ name := (name! "x"), declaredType := some "integer", constraints := [.primaryKey false] }] []])).map
  (fun object => match object.entry with | .table table => table.rowidAlias | .index _ => none) == [some 0]
#guard (catalogOf (schema [.createTable (name! "t") [column (name! "x") (some "INTEGER")] [.primaryKey [(name! "x")]]])).map (·.entry)
  == [.table { columns := [{ name := (name! "x"), declaredType := some "INTEGER" }], primaryKey := [0], rowidAlias := some 0 }]
#guard (catalogOf (schema [.createTable (name! "t") [{ name := (name! "x"), declaredType := some "INTEGER", constraints := [.primaryKey true] }] []])).map (·.entry)
  == [.table { columns := [{ name := (name! "x"), declaredType := some "INTEGER" }], primaryKey := [0], primaryKeyDescending := true }]
#guard !restricted (schema [.createTable (name! "t") [{ name := (name! "x"), declaredType := some "BIGINT", constraints := [.primaryKey false] }] []])

/-- Column {lit}`a` with one column constraint and no declared type. -/
def constrained (constraint : ColumnConstraint) : ColumnDefinition :=
  { name := (name! "a"), declaredType := none, constraints := [constraint] }

-- Constraints of one index merge (slice 5d): the explicit algorithm wins; two different
-- explicit algorithms are SQLite's prepare error.
#guard (catalogOf (schema [.createTable (name! "t") [constrained (.unique (some .replace))] [.unique [(name! "a")]]])).map (·.entry) ==
  [.table { columns := [{ name := (name! "a"), declaredType := none }], uniqueKeys := [[0]], uniqueAlgorithms := [some .replace] }]
#guard statements (schema [.createTable (name! "t") [constrained (.primaryKey false (some .ignore))] [.unique [(name! "a")] (some .replace)]])
  matches [.prepareError (.expression .conflictingAlgorithms)]

-- ASCII-only folding: "Ab" and "aB" are one name; "É" and "é" are two.
#guard statements (migration [] [.createTable (name! "Ab") [column (name! "x")] [], .createTable (name! "aB") [column (name! "x")] []])
  matches [_, .prepareError (.tableExists (name! "aB"))]
#guard (catalogOf (migration [] [.createTable (name! "É") [column (name! "x")] [], .createTable (name! "é") [column (name! "x")] []])).length == 2

-- One namespace: a table and an index cannot share a name.
#guard statements (schema [.createTable (name! "t") [column (name! "a")] [], .createIndex (name! "t") false (name! "t") [(name! "a")]])
  matches [_, .prepareError (.tableNameUsed (name! "t"))]
#guard statements (schema [.createTable (name! "t") [column (name! "a")] [], .createIndex (name! "i") false (name! "t") [(name! "a")], .createTable (name! "I") [column (name! "a")] []])
  matches [_, _, .prepareError (.indexNameUsed (name! "I"))]

-- Column limit from the profile: 3 columns pass, 4 fail; ADD COLUMN to a full table fails.
#guard !(statements (migration [] [.createTable (name! "t") [column (name! "a"), column (name! "b"), column (name! "c")] []] lowered)
  matches [.prepareError _])
#guard statements (migration [] [.createTable (name! "t") [column (name! "a"), column (name! "b"), column (name! "c"), column (name! "d")] []] lowered)
  == [.prepareError (.expression (.tooManyColumns (name! "t")))]
#guard statements (migration [] [.createTable (name! "t") [column (name! "a"), column (name! "b"), column (name! "c")] [], .addColumn (name! "t") (column (name! "d"))] lowered)
  matches [_, .prepareError (.expression (.tooManyColumns (name! "t")))]

-- Two errors in one statement: SQLite reports the first check that fails, column by column.
#guard statements (migration [] [.createTable (name! "t") [column (name! "a"), column (name! "A"), column (name! "b"), column (name! "c")] []] lowered)
  == [.prepareError (.expression (.duplicateColumn (name! "A")))]
#guard statements (migration [] [.createTable (name! "t") [column (name! "a"), column (name! "b"), column (name! "c"), column (name! "c")] []] lowered)
  == [.prepareError (.expression (.tooManyColumns (name! "t")))]

-- ADD COLUMN: a missing table, a used name, and the appended column.
#guard statements (migration tableT [.addColumn (name! "u") (column (name! "c")), .addColumn (name! "T") (column (name! "A")), .addColumn (name! "t") (column (name! "c"))])
  == [.prepareError (.noSuchTable (name! "u")), .prepareError (.expression (.duplicateColumn (name! "A"))), .addColumn 0 { name := (name! "c"), declaredType := some "TEXT" }]

-- INSERT: errors in SQLite's order, and full rows with defaults and converted literals.
#guard statements (migration tableT [.insert (name! "u") none [[.null]] [], .insert (name! "t") (some [(name! "z")]) [[.null]] [],
    .insert (name! "t") none [[.null]] [], .insert (name! "t") (some [(name! "a")]) [[.null, .null]] [], .insert (name! "t") none [[.null], [.null, .null]] []])
  == [.prepareError (.noSuchTable (name! "u")), .prepareError (.expression (.tableHasNoColumn (name! "t") (name! "z"))),
      .prepareError (.expression (.valueCount (name! "t") 2 1)), .prepareError (.expression (.valuesForColumns 2 1)), .prepareError (.expression .valuesDiffer)]
#guard statements (migration tableT [.insert (name! "t") (some [(name! "B")]) [[.numeric "1_000"], [.numeric "0x10"], [.negate (.numeric "9223372036854775808")]] []])
  == [.insert 0 [[.value .null, .value (.integer 1000)], [.value .null, .value (.integer 16)], [.value .null, .value (.integer (-9223372036854775808))]] []]
#guard statements (migration tableT [.insert (name! "t") (some [(name! "b")]) [[.numeric "9223372036854775808"]] []])
  == [.insert 0 [[.value .null, .value (.real (9223372036854775808.0 : Float).toBits)]] []]
#guard statements (migration tableT [.insert (name! "t") (some [(name! "b")]) [[.numeric "0x10000000000000000"]] []])
  == [.prepareError (.expression (.hexLiteralTooBig "0x10000000000000000"))]

-- Double-quoted strings: a string literal when DQS_DML is on, else "no such column".
#guard statements (migration tableT [.insert (name! "t") (some [(name! "a")]) [[.identifier (name! "x") .double]] []])
  == [.insert 0 [[.value (.text [120]), .value .null]] []]
#guard statements (migration tableT [.insert (name! "t") (some [(name! "a")]) [[.identifier (name! "x") .double]] []] { defaults with dqsDml := false })
  == [.prepareError (.expression (.noSuchColumn (name! "x")))]

-- UPDATE: SET and WHERE names, and the modeled integer equality filter.
#guard statements (migration tableT [.update (name! "t") [((name! "z"), .null)] none, .update (name! "t") [((name! "a"), .null)] (some (.compare .eq (.identifier (name! "z") .none) (.numeric "1"))),
    .update (name! "t") [((name! "A"), .string [111])] (some (.compare .eq (.identifier (name! "b") .none) (.numeric "7")))])
  == [.prepareError (.expression (.noSuchColumn (name! "z"))), .prepareError (.expression (.noSuchColumn (name! "z"))),
      .update 0 [(0, .literal (.text [111]))] (some (.compare .eq (some .integer) (.column 1) (.literal (.integer 7)))) []]
-- A TEXT column against a number compares with TEXT affinity (R-29161-32953).
#guard statements (migration tableT [.update (name! "t") [((name! "a"), .null)] (some (.compare .eq (.identifier (name! "a") .none) (.numeric "1")))])
  == [.update 0 [(0, .literal .null)] (some (.compare .eq (some .text) (.column 0) (.literal (.integer 1)))) []]

/-- A table with keys over integer-comparable columns: a primary key, a UNIQUE
constraint, a unique index and an index that is not unique. -/
def keyed : Catalog := catalogOf (schema [.createTable (name! "k") [column (name! "a") (some "INTEGER"), column (name! "b") (some "NUMERIC"),
    column (name! "c") (some "BIGINT"), column (name! "d")] [.primaryKey [(name! "c")], .unique [(name! "b"), (name! "a")]],
  .createIndex (name! "ka") true (name! "k") [(name! "a")], .createIndex (name! "kb") false (name! "k") [(name! "b")]])

-- The unique keys of a table, which writes keep: the primary key, UNIQUE constraints, then
-- unique indexes. A write names only the table; execution reads the keys from the catalog.
#guard (keyed.findTable (name! "k")).map (fun (position, table) => keyed.uniqueKeys position table) ==
  some [[2], [1, 0], [0]]
#guard statements (migration keyed [.insert (name! "k") none [[.null, .null, .null, .null]] [], .update (name! "k") [((name! "a"), .null)] none])
  == [.insert 0 [[.value .null, .value .null, .value .null, .value .null]] [], .update 0 [(0, .literal .null)] none []]

-- Keys of every affinity and value run (slice 5a): text values and TEXT key columns.
#guard !restricted (migration keyed [.insert (name! "k") (some [(name! "a"), (name! "d")]) [[.null, .null], [.string [120], .null]] []])
#guard !restricted (migration keyed [.update (name! "k") [((name! "d"), .string [49]), ((name! "c"), .string [120])] none])
#guard !restricted (migration (catalogOf (schema [.createTable (name! "s") [column (name! "a")] [.unique [(name! "a")]]]))
  [.insert (name! "s") none [[.null]] []])

-- New tables and indexes take the next catalog position.
#guard statements (schema [.createTable (name! "t") [column (name! "a")] [], .createIndex (name! "i") false (name! "t") [(name! "a")], .createTable (name! "u") [column (name! "a")] []])
  matches [.createTable 0 (name! "t") _, .createIndex 1 (name! "i") _, .createTable 2 (name! "u") _]

-- Transactions: ROLLBACK restores the catalog of BEGIN; COMMIT keeps the changes.
#guard statements (migration [] [.begin, .createTable (name! "t") [column (name! "a")] [], .rollback, .createTable (name! "t") [column (name! "a")] []])
  matches [.begin, .createTable .., .rollback, .createTable ..]
#guard statements (migration [] [.begin, .createTable (name! "t") [column (name! "a")] [], .commit, .createTable (name! "t") [column (name! "a")] []])
  matches [.begin, .createTable .., .commit, .prepareError (.tableExists (name! "t"))]

-- A statement after a prepare error resolves as if that statement had no effect.
#guard statements (migration tableT [.createTable (name! "t") [column (name! "x")] [], .addColumn (name! "t") (column (name! "c"))])
  matches [.prepareError (.tableExists (name! "t")), .addColumn 0 _]

-- Statements that run keep the model scope; descriptions may contain the statistics tables.
#guard restricted (migration [] [.createTable (name! "t") [{ name := (name! "a"), declaredType := none, constraints := [.notNull] }] []])
#guard restricted (migration tableT [.createIndex (name! "i") false (name! "t") [(name! "a")]])
#guard statements (migration [] [.createTable (name! "sqlite_x") [column (name! "a")] []]) == [.prepareError (.expression (.reservedName (name! "sqlite_x")))]
#guard !restricted (schema [.createTable (name! "sqlite_stat1") [column (name! "tbl") none, column (name! "idx") none, column (name! "stat") none] []])

-- A schema describes the starting catalog, then the script resolves against it.
#guard (resolveSchemaAndScript defaults [.createTable (name! "t") [column (name! "a")] []] [.insert (name! "t") none [[.null]] []]).toOption.map
    (fun resolution => (resolution.startCatalog.length, resolution.resolved, resolution.nextCatalog.length))
  == some (1, [.insert 0 [[.value .null]] []], 1)
#guard resolveSchemaAndScript defaults [.createTable (name! "t") [column (name! "a")] [], .insert (name! "t") none [[.null]] []] []
  matches .error (.schemaRestricted { statement := 1, path := [], .. })
#guard resolveSchemaAndScript defaults [.createTable (name! "t") [column (name! "a")] [], .createTable (name! "T") [column (name! "a")] []] []
  matches .error (.schemaPrepareError 1 (.tableExists (name! "T")))
#guard resolveSchemaAndScript defaults [] [.createTable (name! "t") [column (name! "rowid")] []]
  matches .error (.scriptRestricted { statement := 0, path := [1], .. })
#guard (ExprError.valueCount (name! "t") 2 1).message == "table t has 2 columns but 1 values were supplied"

end Belay.Sqlite.Resolution.Examples
