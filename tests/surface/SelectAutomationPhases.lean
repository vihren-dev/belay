import SelectAutomationPhaseRules
import SelectAutomationPhaseBridge

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! ADR 0027's two prototype proofs through the phase rules (deep review, finding 6): the
schema projection of {lit}`SelectAutomationSchema`, and a grouped query with {lit}`HAVING`.
Neither proof unfolds a whole-query law; each reads the rules of
{lit}`SelectAutomationPhaseRules` and the bridge of {lit}`SelectAutomationPhaseBridge`. -/

namespace SelectAutomation
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-! Proof 1: the schema projection of {lit}`SelectAutomationSchema.schema_projection`, through
the rules. -/

/-- For every valid database, a present NOT NULL column projected by a calm simple
single-statement SELECT gives one successful rows output, and every returned row has
one non-NULL cell. The same statement as {lit}`SelectAutomationSchema.schema_projection`.
Proof sketch: {name}`outputs_of_calm_table` and {name}`possibleResults_noWindow` give the
output; the rules {name}`mem_results`, {name}`mem_uniqueRecords`, {name}`mem_records_scalar`
and {name}`Resolved.mem_filtered` trace each row to a stored row, which validity and the
NOT NULL fact constrain. No whole-query law is unfolded. -/
theorem schema_projection_phases (script : Script) (db : Database)
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
  rw [outputs_of_calm_table script db _ isQuery head resolved rfl present calm rfl rfl rfl rfl
    (by simp [Resolved.Query.fails, Resolved.Query.simple])]
  rw [possibleResults_noWindow _ _ _ rfl rfl rfl, Output.ofResults_singleton]
  refine ⟨_, rfl, ?_⟩
  intro row member
  have member := (Resolved.stableSort_perm _ _).mem_iff.mp member
  obtain ⟨record, unique, rfl⟩ := mem_results _ _ _ _ member
  obtain ⟨source, kept, output⟩ := mem_records_scalar _ _ _ _ rfl (mem_uniqueRecords _ _ _ _ rfl unique)
  obtain ⟨original, _⟩ := (Resolved.mem_filtered _ _ _ source).mp kept
  obtain ⟨stored, storedIn, rfl⟩ := (mem_sourceRows_iff table source).mp original
  have wide := db.valid.admitted.rowsWide position table present stored storedIn
  have inside : columnIndex < stored.values.length := by
    rw [wide]
    exact (List.getElem?_eq_some_iff.mp columnAt).1
  have nonnull := db.notNull position table present stored storedIn columnIndex column
    stored.values[columnIndex] columnAt (List.getElem?_eq_getElem inside) required
  refine ⟨stored.values[columnIndex], ?_, nonnull⟩
  rw [output]
  simp [Resolved.Query.simple, Resolved.Expr.eval_column, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem inside]

/-! Proof 2: a grouped query with {lit}`HAVING`, through the rules. -/

/-- The resolved form of {lit}`SELECT c, count(*) FROM t GROUP BY c HAVING c IS NOT NULL` over
the table at a catalog position whose first column has TEXT affinity: an aggregate query grouped
by the first column under {lit}`BINARY`, with the column and the row count as result columns,
and {lit}`IS NOT NULL` of the column as {lit}`HAVING`. -/
def groupedQuery (position : Nat) : Resolved.Query :=
  { sources := [.first position], filter := none, aggregate := true, groupBy := [(.column 0, .binary)],
    columns := [.scalar (.column 0), .aggregate .countRows], names := ["c", "count(*)"], orderBy := [], offset := 0,
    limit := none, having := some (.compare .isNot (some .text) (.column 0) (.literal .null) .binary) }

/-- For every value, {lit}`IS NOT NULL` of the value under TEXT affinity is true exactly when the
value is not NULL. Proof sketch: cases on the value; {name}`Resolved.comparisonOperands` keeps
the NULL literal, and {name}`Comparison.apply` of {lit}`IS NOT` with a NULL operand tests the
other operand. -/
theorem isNotNull_truthy (value : Value) :
    Resolved.truthy (Comparison.apply .isNot (Resolved.comparisonOperands (some .text) value .null).1
      (Resolved.comparisonOperands (some .text) value .null).2 .binary) = true ↔ value ≠ .null := by
  cases value <;> simp [Resolved.comparisonOperands, Comparison.apply, Value.store, Value.isNull, Value.isText,
    truth, Resolved.truthy]

/-- For every context, catalog position, rows and possible result of the grouped query
({name}`groupedQuery`) over the rows, every row of the result is the first cell of some source
row and a count of at least one, and that cell is not NULL. Proof sketch: the rules
{name}`possibleResults_noWindow`, {name}`mem_results`, {name}`mem_uniqueRecords`,
{name}`mem_records_aggregate`, {name}`mem_queryGroups` and {name}`groupRow_mem` trace the row
to the row of a nonempty group within the rows; {name}`isNotNull_truthy` reads {lit}`HAVING`
and {name}`Resolved.countRows_eval` the count. -/
theorem grouped_rows (context : Resolved.EvalContext) (position : Nat) (rows : List (List Value))
    (result : List (List Value)) (member : result ∈ (groupedQuery position).possibleResults context rows) :
    ∀ row ∈ result, ∃ source ∈ rows, ∃ count : Nat, 1 ≤ count ∧
      row = [source.getD 0 .null, .integer count] ∧ source.getD 0 .null ≠ .null := by
  rw [possibleResults_noWindow _ _ _ rfl rfl rfl, List.mem_singleton] at member
  subst member
  intro row member
  have member := (Resolved.stableSort_perm _ _).mem_iff.mp member
  obtain ⟨record, unique, rfl⟩ := mem_results _ _ _ _ member
  obtain ⟨group, inGroups, having, output⟩ := mem_records_aggregate _ _ _ _ rfl (mem_uniqueRecords _ _ _ _ rfl unique)
  obtain ⟨nonempty, within⟩ := mem_queryGroups _ _ _ (by simp [groupedQuery]) group inGroups
  have source := groupRow_mem context (groupedQuery position) group rfl nonempty
  obtain ⟨original, _⟩ := (Resolved.mem_filtered _ _ _ _).mp (within _ source)
  refine ⟨_, original, group.length, ?_, ?_, ?_⟩
  · cases group with
    | nil => exact absurd rfl nonempty
    | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
  · rw [output]
    simp [groupedQuery, Resolved.Expr.eval_column, Resolved.countRows_eval]
  · simp only [groupedQuery, Option.all_some, Resolved.Expr.eval_compare, Resolved.Expr.eval_column,
      Resolved.Expr.eval_literal] at having
    exact (isNotNull_truthy _).mp having

/-- For every database and single-statement script whose statement resolves to the grouped
query ({name}`groupedQuery`) of a present table, calm, the run's outputs are one rows output,
and every row of it is the first cell of a stored row of the table with a count of at least
one, and that cell is not NULL. Proof sketch: {name}`outputs_of_calm_table` with
{name}`possibleResults_noWindow` gives the rows output; {name}`grouped_rows` constrains each
row; {name}`mem_sourceRows_iff` names the stored row. -/
theorem grouped_outputs (script : Script) (db : Database) {statement : Syntax.Statement}
    {parameters : List Value} {after : ResolveState} {position : Nat} {table : Table}
    (isQuery : script.isQuery = true)
    (head : script.statements = [(statement, parameters)])
    (resolved : resolveStatement runContext db.raw.connection.resolveState statement =
      .ok (.query (groupedQuery position) [], after))
    (present : db.raw.table position = some table)
    (calm : (Resolved.Statement.query (groupedQuery position) []).Calm) :
    ∃ rows, (db.run script).outputs = [.rows rows] ∧
      ∀ row ∈ rows, ∃ stored ∈ table.rows, ∃ count : Nat, 1 ≤ count ∧
        row = [stored.values.getD 0 .null, .integer count] ∧ stored.values.getD 0 .null ≠ .null := by
  fail_if_success sql_auto
  rw [outputs_of_calm_table script db _ isQuery head resolved rfl present calm rfl rfl rfl rfl
    (by simp [Resolved.Query.fails, groupedQuery, Resolved.Aggregate.fails])]
  rw [possibleResults_noWindow _ _ _ rfl rfl rfl, Output.ofResults_singleton]
  refine ⟨_, rfl, fun row member => ?_⟩
  obtain ⟨source, original, count, positive, shape, nonnull⟩ :=
    grouped_rows (Resolved.EvalContext.bound parameters) position (Resolved.sourceRows table) _
      (by rw [possibleResults_noWindow _ _ _ rfl rfl rfl]; exact List.mem_singleton.mpr rfl) row member
  obtain ⟨stored, storedIn, rfl⟩ := (mem_sourceRows_iff table source).mp original
  exact ⟨stored, storedIn, count, positive, shape, nonnull⟩

/-- D2's observer over the grouped query: the one output of {name}`grouped_outputs` satisfies the
row property ({name}`OutputSatisfies`), through {name}`ofResults_satisfies` over every possible
result. The quantifier over results is the shape of a D2 continuation; here the list has one
result. Proof sketch: {name}`outputs_of_calm_table`, {name}`Resolved.Query.possibleResults_ne_nil`
and {name}`grouped_rows`. -/
theorem grouped_observer (script : Script) (db : Database) {statement : Syntax.Statement}
    {parameters : List Value} {after : ResolveState} {position : Nat} {table : Table}
    (isQuery : script.isQuery = true)
    (head : script.statements = [(statement, parameters)])
    (resolved : resolveStatement runContext db.raw.connection.resolveState statement =
      .ok (.query (groupedQuery position) [], after))
    (present : db.raw.table position = some table)
    (calm : (Resolved.Statement.query (groupedQuery position) []).Calm) :
    ∃ output, (db.run script).outputs = [output] ∧ OutputSatisfies (fun result => ∀ row ∈ result,
      ∃ source ∈ Resolved.sourceRows table, ∃ count : Nat, 1 ≤ count ∧
        row = [source.getD 0 .null, .integer count] ∧ source.getD 0 .null ≠ .null) output := by
  rw [outputs_of_calm_table script db _ isQuery head resolved rfl present calm rfl rfl rfl rfl
    (by simp [Resolved.Query.fails, groupedQuery, Resolved.Aggregate.fails])]
  exact ⟨_, rfl, ofResults_satisfies _ _ (Resolved.Query.possibleResults_ne_nil _ _ _)
    (fun result member => grouped_rows _ position _ result member)⟩

/-- A table with two groups, one of them NULL, for the non-vacuity witness. -/
def groupedTable : Database := db! r"
  CREATE TABLE t(c TEXT, n INTEGER);
  INSERT INTO t VALUES ('a', 1), ('a', 2), (NULL, 3);"

/-- The concrete SQL text of the grouped query. -/
def groupedScript : Script := sql r"SELECT c, count(*) FROM t GROUP BY c HAVING c IS NOT NULL"

/-- The grouped script over the table gives the one group that is not NULL with its count, and
the table is present: the universal claims are not instantiated only through an empty result. -/
theorem grouped_witness :
    (groupedTable.run groupedScript).outputs = [.rows [[.text [97], .integer 2]]] ∧
    (groupedTable.raw.table 0).isSome = true := by
  decide +kernel

/-- Every premise of {name}`grouped_outputs` is inhabited by the concrete table and script, and
applying that theorem gives its claim for them. Proof sketch: the resolution and presence facts
reduce in the kernel; the calm proof reads the three expressions of the statement. -/
theorem grouped_instance :
    ∃ rows, (groupedTable.run groupedScript).outputs = [.rows rows] ∧
      ∀ row ∈ rows, ∃ stored ∈ ((groupedTable.raw.table 0).get (by decide +kernel)).rows, ∃ count : Nat, 1 ≤ count ∧
        row = [stored.values.getD 0 .null, .integer count] ∧ stored.values.getD 0 .null ≠ .null :=
  grouped_outputs groupedScript groupedTable (position := 0) (after := groupedTable.raw.connection.resolveState)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by
      intro expression member
      change expression ∈ [Resolved.Expr.column 0, Resolved.Expr.column 0,
        Resolved.Expr.compare .isNot (some .text) (.column 0) (.literal .null) .binary] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact Resolved.Expr.calm_column 0
      · exact Resolved.Expr.calm_column 0
      · exact (Resolved.Expr.calm_compare ..).mpr ⟨Resolved.Expr.calm_column 0, Resolved.Expr.calm_literal .null⟩)

#print axioms schema_projection_phases
#print axioms grouped_rows
#print axioms grouped_outputs
#print axioms grouped_observer
#print axioms grouped_instance

end SelectAutomation
