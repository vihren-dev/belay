import SchemaStepLaws

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! A fixture module of {lit}`tests/surface_schema_script_test.py`: the success law of INSERT from a query (ADR 0017,
S6, task {lit}`20261027-schema-script-laws`) on a concrete database. The statement copies the two columns of the
table {lit}`src` into the empty table {lit}`dst`. The first example instantiates every premise of the law and reads the
database after the step. The four failing examples change the target or the source so that one premise of the
law fails (a NULL in a NOT NULL column, a duplicate key, a CHECK failure, a type mismatch of a STRICT table): the
statement fails with the constraint error and the rows do not fit the target. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace InsertSelectExamples
open SchemaStepLaws

/-- The source table {lit}`src` and the targets of the examples: an empty table with a NOT NULL column, a table with
a UNIQUE column that holds a name, a table with a CHECK constraint on the id, a STRICT table with an INTEGER column,
and a table {lit}`holes` with a NULL name. -/
def warehouse : Belay.Sqlite.Database := db! r"
  CREATE TABLE src(id INTEGER PRIMARY KEY, name TEXT);
  INSERT INTO src VALUES(1,'a'),(2,'b');
  CREATE TABLE dst(id INTEGER PRIMARY KEY, name TEXT NOT NULL);
  CREATE TABLE holes(id INTEGER PRIMARY KEY, name TEXT);
  INSERT INTO holes VALUES(1,NULL);
  CREATE TABLE dstUnique(id INTEGER PRIMARY KEY, name TEXT UNIQUE);
  INSERT INTO dstUnique VALUES(9,'a');
  CREATE TABLE dstChecked(id INTEGER PRIMARY KEY, name TEXT CHECK(id < 2));
  CREATE TABLE dstStrict(id INTEGER PRIMARY KEY, n INTEGER) STRICT;"

/-- The connection of the warehouse with foreign keys off. -/
def begin : Connection := warehouse.raw.connection environment.counters

/-- The INSERT that copies the two columns of {lit}`src` into {lit}`dst`. -/
def okStatement : Syntax.Statement := statementOf (sql r"INSERT INTO dst SELECT id, name FROM src;")


/-- The query of the INSERT: a plain scan of the table {lit}`src`, which is at position 0, with its two columns. -/
def scanQuery : Resolved.Query :=
  Resolved.Query.simple [Resolved.QuerySource.first 0] none [.scalar (.column 0), .scalar (.column 1)] ["id", "name"]

/-- The resolved INSERT: the table {lit}`dst` at position 1 takes the cells of the query in order. -/
def okResolved : Resolved.Statement :=
  .insertSelect 1 [.source 0, .source 1] scanQuery [] [] none [] none

/-- The statement resolves to the INSERT of {lean}`okResolved`. Proof sketch: kernel evaluation. -/
theorem ok_resolves : resolvesTo begin okStatement okResolved = true := by decide +kernel

/-- The target table. -/
def dstTable : Table := (begin.state.database.table 1).get (by decide +kernel)

/-- The source table. -/
def srcTable : Table := (begin.state.database.table 0).get (by decide +kernel)

/-- The database has the target table at position 1. Proof sketch: by the definition of the table. -/
theorem dst_present : begin.state.database.table 1 = some dstTable := (Option.some_get _).symm

/-- The database has the source table at position 0. Proof sketch: by the definition of the table. -/
theorem src_present : begin.state.database.table 0 = some srcTable := (Option.some_get _).symm

/-- The context of the query when the statement runs with the constant clock and no parameter. -/
def runContext' : Resolved.EvalContext :=
  Resolved.statementContext 0 (begin.state.counters.view okResolved.counterReads) [] begin.state.database []

/-- The rows that the query hands over: the pair of id and name of each row of the source. -/
def selected : List (List Value) := [[.integer 1, .text [97]], [.integer 2, .text [98]]]

/-- The query is simple. Proof sketch: it is {name}`Resolved.Query.simple`. -/
theorem scan_simple : scanQuery.Simple := Resolved.Query.simple_isSimple _ _ _ _

/-- The context of the query has no subquery, so it is quiet. Proof sketch: by definition, the context has no
subquery fault. -/
theorem context_quiet : runContext'.Quiet := fun _ _ => ⟨rfl, rfl, rfl⟩

/-- The productions of the query are one, with the rows of {lean}`selected` and no failure. Proof sketch:
{name}`Resolved.Query.productions_scan_single` with the one access order of the source, and the kernel for the
rows. -/
theorem certain : scanQuery.productions runContext' begin.state.database
    (!Resolved.Statement.collectsSource 1 scanQuery [] [] none) = some [{ rows := selected, failure := none }] := by
  have single : Table.accessOrders begin.state.database.catalog 0 srcTable = [srcTable.scanRows] :=
    Table.accessOrders_single _ _ _ (by decide +kernel)
  have rows : scanQuery.results runContext' (Resolved.sourceRows srcTable) = selected := by decide +kernel
  rw [scanQuery.productions_scan_single runContext' begin.state.database 0 srcTable _ rfl
    scan_simple (by decide +kernel) context_quiet src_present single, rows]

/-- The full rows that the INSERT writes for the rows of the query. -/
def written : List (List Value) :=
  insertSelectRows runContext' dstTable.shape.columns [.source 0, .source 1] selected

/-- The written rows are the two pairs of id and name, as the SQL text shows. Proof sketch: kernel evaluation. -/
theorem written_rows : written = [[.integer 1, .text [97]], [.integer 2, .text [98]]] := by decide +kernel

/-- The written rows fit the target: every field of {name}`InsertFits` holds. Proof sketch: kernel evaluation of
each field on the target table, which is empty and has the primary key and the NOT NULL column. -/
theorem written_fit : InsertFits (begin.state.database.keys 1 dstTable) dstTable written where
  aliasFree := by decide +kernel
  aliasInteger := by decide +kernel
  stored := by decide +kernel
  notNull := by decide +kernel
  typed := by decide +kernel
  checked := by decide +kernel
  keysDistinct := by decide +kernel
  rowidsDistinct := by decide +kernel
  rowidsBounded := by decide +kernel

/-- Success law of INSERT from a query: the step continues without an error, with no other execution, and the
database after it is the database with the target rows of the table with the two rows appended. The ten premises
of the general law are the facts above and kernel checks of the clauses. Proof sketch:
{name}`runScriptStep_insertSelect_success`. -/
theorem insert_select_appends_the_rows : ∃ output next, stepOf begin okStatement = .continued output next [] ∧
    output.isError = false ∧ next.state.database = begin.state.database.setRows 1
      (LiteralData.inserted dstTable written).rows := by
  obtain ⟨after, found⟩ := resolvesTo_sound ok_resolves
  exact runScriptStep_insertSelect_success (value := 0) (table := dstTable) (rows := selected) found
    (by decide +kernel) (by decide +kernel) dst_present certain written_fit (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

-- The failing cases: each premise of the success law is needed

/-- The target table and the full rows that the INSERT of the two columns of the source table would write, for the
tables that two names find. -/
def writtenFor (target source : Identifier) : Option (Nat × Table × List (List Value)) :=
  (begin.state.database.tableNamed target).bind fun (position, targetTable) =>
    (begin.state.database.tableNamed source).map fun (_, sourceTable) =>
      (position, targetTable, insertSelectRows runContext' targetTable.shape.columns [.source 0, .source 1]
        (scanQuery.results runContext' (Resolved.sourceRows sourceTable)))

/-- If a field of {name}`InsertFits` is false for the rows, the rows do not fit. The field is the NOT NULL check. -/
theorem not_fit_of_notNull {keys : List UniqueKey} {table : Table} {rows : List (List Value)}
    (failing : LiteralData.notNullRows (LiteralData.inserted table rows) = false) : ¬ InsertFits keys table rows :=
  fun fits => by simp [fits.notNull] at failing

/-- If a field of {name}`InsertFits` is false for the rows, the rows do not fit. The field is the key check. -/
theorem not_fit_of_keys {keys : List UniqueKey} {table : Table} {rows : List (List Value)}
    (failing : LiteralData.keysUnique keys (LiteralData.inserted table rows) = false) : ¬ InsertFits keys table rows :=
  fun fits => by simp [fits.keysDistinct] at failing

/-- If a field of {name}`InsertFits` is false for the rows, the rows do not fit. The field is the CHECK check. -/
theorem not_fit_of_check {keys : List UniqueKey} {table : Table} {rows : List (List Value)}
    (failing : LiteralData.checkedRows (LiteralData.inserted table rows) = false) : ¬ InsertFits keys table rows :=
  fun fits => by simp [fits.checked] at failing

/-- If a field of {name}`InsertFits` is false for the rows, the rows do not fit. The field is the STRICT type check. -/
theorem not_fit_of_type {keys : List UniqueKey} {table : Table} {rows : List (List Value)}
    (failing : LiteralData.typedRows (LiteralData.inserted table rows) = false) : ¬ InsertFits keys table rows :=
  fun fits => by simp [fits.typed] at failing

/-- Failing case of the success law, a NULL name in a NOT NULL column: the INSERT fails with the constraint error 19, and the rows that
the query hands over do not fit the target, so the premise {lit}`fits` of the law cannot hold. Proof sketch: kernel
evaluation of the step and of the field of {name}`InsertFits` that the case violates. -/
theorem null_into_not_null : outputOf begin (statementOf (sql r"INSERT INTO dst SELECT id, name FROM holes;")) = some (.error 19) ∧
    ∀ position table rows, writtenFor (name! "dst") (name! "holes") = some (position, table, rows) →
      ¬ InsertFits (begin.state.database.keys position table) table rows := by
  refine ⟨by decide +kernel, fun position table rows same => ?_⟩
  have check : ((writtenFor (name! "dst") (name! "holes")).map (fun (_, t, r) => LiteralData.notNullRows (LiteralData.inserted t r))) = some false := by decide +kernel
  rw [same] at check
  exact not_fit_of_notNull (Option.some.inj check)

/-- Failing case of the success law, a name that the UNIQUE column of the target already has: the INSERT fails with the constraint error 19, and the rows that
the query hands over do not fit the target, so the premise {lit}`fits` of the law cannot hold. Proof sketch: kernel
evaluation of the step and of the field of {name}`InsertFits` that the case violates. -/
theorem duplicate_key : outputOf begin (statementOf (sql r"INSERT INTO dstUnique SELECT id, name FROM src;")) = some (.error 19) ∧
    ∀ position table rows, writtenFor (name! "dstUnique") (name! "src") = some (position, table, rows) →
      ¬ InsertFits (begin.state.database.keys position table) table rows := by
  refine ⟨by decide +kernel, fun position table rows same => ?_⟩
  have check : ((writtenFor (name! "dstUnique") (name! "src")).map (fun (position, t, r) => LiteralData.keysUnique (begin.state.database.keys position t) (LiteralData.inserted t r))) = some false := by decide +kernel
  rw [same] at check
  exact not_fit_of_keys (Option.some.inj check)

/-- Failing case of the success law, an id that the CHECK constraint of the target refuses: the INSERT fails with the constraint error 19, and the rows that
the query hands over do not fit the target, so the premise {lit}`fits` of the law cannot hold. Proof sketch: kernel
evaluation of the step and of the field of {name}`InsertFits` that the case violates. -/
theorem check_failure : outputOf begin (statementOf (sql r"INSERT INTO dstChecked SELECT id, name FROM src;")) = some (.error 19) ∧
    ∀ position table rows, writtenFor (name! "dstChecked") (name! "src") = some (position, table, rows) →
      ¬ InsertFits (begin.state.database.keys position table) table rows := by
  refine ⟨by decide +kernel, fun position table rows same => ?_⟩
  have check : ((writtenFor (name! "dstChecked") (name! "src")).map (fun (_, t, r) => LiteralData.checkedRows (LiteralData.inserted t r))) = some false := by decide +kernel
  rw [same] at check
  exact not_fit_of_check (Option.some.inj check)

/-- Failing case of the success law, a text value for an INTEGER column of a STRICT table: the INSERT fails with the constraint error 19, and the rows that
the query hands over do not fit the target, so the premise {lit}`fits` of the law cannot hold. Proof sketch: kernel
evaluation of the step and of the field of {name}`InsertFits` that the case violates. -/
theorem strict_mismatch : outputOf begin (statementOf (sql r"INSERT INTO dstStrict SELECT id, name FROM src;")) = some (.error 19) ∧
    ∀ position table rows, writtenFor (name! "dstStrict") (name! "src") = some (position, table, rows) →
      ¬ InsertFits (begin.state.database.keys position table) table rows := by
  refine ⟨by decide +kernel, fun position table rows same => ?_⟩
  have check : ((writtenFor (name! "dstStrict") (name! "src")).map (fun (_, t, r) => LiteralData.typedRows (LiteralData.inserted t r))) = some false := by decide +kernel
  rw [same] at check
  exact not_fit_of_type (Option.some.inj check)

#print axioms certain
#print axioms insert_select_appends_the_rows
#print axioms null_into_not_null
#print axioms duplicate_key
#print axioms check_failure
#print axioms strict_mismatch

end InsertSelectExamples
