import SelectAutomationCore

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! ADR 0027's schema experiment uses the existing table-output law. The theorem is
universal over databases; the concrete examples check that its premises are inhabited. -/

namespace SelectAutomation
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- For every valid database, a present NOT NULL column projected by a calm simple
single-statement SELECT gives one successful rows output, and every returned row has
one non-NULL cell. The filter may discard every row; the table may be empty. The
resolution, table presence and calmness assumptions are required.
Proof sketch: the table-output law gives the exact output. Validity supplies each
source cell and excludes NULL; filter membership and projection transport that fact. -/
theorem schema_projection (script : Script) (db : Database)
    {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {position columnIndex : Nat} {table : Table} {column : CatalogColumn}
    {filter : Option Resolved.Expr} {label : String}
    (isQuery : script.isQuery = true)
    (head : script.statements = [(statement, parameters)])
    (resolved : resolveStatement runContext db.raw.connection.resolveState statement =
      .ok (.query (Resolved.Query.simple [.first position] filter
        [.scalar (.column columnIndex)] [label]) [], after))
    (present : db.raw.table position = some table)
    (columnAt : table.shape.columns[columnIndex]? = some column)
    (required : column.notNull = true)
    (calm : (Resolved.Statement.query (Resolved.Query.simple [.first position] filter
      [.scalar (.column columnIndex)] [label]) []).Calm) :
    ∃ rows, (db.run script).outputs = [.rows rows] ∧
      ∀ row ∈ rows, ∃ value, row = [value] ∧ value ≠ .null := by
  fail_if_success sql_auto [db.notNull]
  have output := Script.outputOn_query script db statement parameters [] _ [] after head resolved
  rw [resolvedStepOutput_simpleTable_rows none 0 position db.raw.connection parameters table filter
    [.scalar (.column columnIndex)] [label] present calm] at output
  rw [Script.query_outputs isQuery db, output]
  refine ⟨_, rfl, ?_⟩
  intro row member
  have member := (Resolved.stableSort_perm _ _).mem_iff.mp member
  rw [(Resolved.Query.simple_isSimple _ _ _ _).results_eq] at member
  obtain ⟨source, kept, rfl⟩ := List.mem_map.mp member
  obtain ⟨original, _⟩ := (Resolved.mem_filtered _ _ _ source).mp kept
  obtain ⟨stored, storedIn, rfl⟩ := (mem_sourceRows_iff table source).mp original
  have wide := db.valid.admitted.rowsWide position table present stored storedIn
  have inside : columnIndex < stored.values.length := by
    rw [wide]
    exact (List.getElem?_eq_some_iff.mp columnAt).1
  have nonnull := db.notNull position table present stored storedIn columnIndex column
    stored.values[columnIndex] columnAt (List.getElem?_eq_getElem inside) required
  refine ⟨stored.values[columnIndex], ?_, nonnull⟩
  simp [Resolved.Query.simple, Resolved.Expr.eval_column, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem inside]

/-- A valid schema with an empty NOT NULL table, for the non-vacuity witness. -/
def emptyCustomers : Database := db! r"CREATE TABLE customers(customer TEXT NOT NULL);"

/-- The same schema with one customer, so the postcondition also constrains a returned cell. -/
def oneCustomer : Database := db! r"
  CREATE TABLE customers(customer TEXT NOT NULL);
  INSERT INTO customers VALUES ('a');"

/-- The concrete SQL text of the motivating projection. -/
def customerQuery : Script := sql r"SELECT customer FROM customers"

/-- Both concrete databases have the required schema and their query succeeds. One output
is empty and the other contains a non-NULL cell; the universal claim is not instantiated
only through an empty result or an impossible schema. -/
theorem schema_witnesses :
    (emptyCustomers.run customerQuery).outputs = [.rows []] ∧
    (oneCustomer.run customerQuery).outputs = [.rows [[.text [97]]]] ∧
    (emptyCustomers.raw.table 0).isSome = true ∧
    (oneCustomer.raw.table 0).isSome = true := by
  decide +kernel

/-- Every premise of {name}`schema_projection` is inhabited by each concrete database,
and applying that theorem gives its full successful-output claim for each one.
Proof sketch: each finite schema and resolution fact reduces in the kernel. -/
theorem schema_instances (db : Database) (sample : db = emptyCustomers ∨ db = oneCustomer) :
    ∃ rows, (db.run customerQuery).outputs = [.rows rows] ∧
      ∀ row ∈ rows, ∃ value, row = [value] ∧ value ≠ .null := by
  rcases sample with rfl | rfl
  · let table := (emptyCustomers.raw.table 0).get (by decide +kernel)
    exact schema_projection customerQuery emptyCustomers
      (position := 0) (columnIndex := 0) (table := table)
      (column := table.shape.columns[0]'(by decide +kernel))
      (filter := none) (label := "customer") (after := emptyCustomers.raw.connection.resolveState)
      (by decide +kernel) rfl rfl (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by
        intro expression member
        change expression ∈ [Resolved.Expr.column 0] at member
        simp only [List.mem_singleton] at member
        subst expression
        exact Resolved.Expr.calm_column 0)
  · let table := (oneCustomer.raw.table 0).get (by decide +kernel)
    exact schema_projection customerQuery oneCustomer
      (position := 0) (columnIndex := 0) (table := table)
      (column := table.shape.columns[0]'(by decide +kernel))
      (filter := none) (label := "customer") (after := oneCustomer.raw.connection.resolveState)
      (by decide +kernel) rfl rfl (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by
        intro expression member
        change expression ∈ [Resolved.Expr.column 0] at member
        simp only [List.mem_singleton] at member
        subst expression
        exact Resolved.Expr.calm_column 0)

#print axioms schema_projection
#print axioms schema_witnesses
#print axioms schema_instances

end SelectAutomation
