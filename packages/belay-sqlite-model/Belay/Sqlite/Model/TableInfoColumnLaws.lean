import Belay.Sqlite.Model.TableInfoLaws
import Belay.Sqlite.Model.Resolution.Catalog

set_option doc.verso true

/-! Catalog columns recovered from the exact metadata of {lit}`pragma_table_info`. -/

namespace Belay.Sqlite.Model

/-- For every list of columns with distinct ASCII-folded names, and every column in
that list, its name resolves to a position containing that column. Without the distinct-name
hypothesis, an earlier column can shadow it. Proof sketch: induction on the list; distinct
names make lookup skip each earlier column. -/
theorem column_lookup_of_member (columns : List CatalogColumn) (column : CatalogColumn)
    (unique : (columns.map (·.name.folded)).Nodup) (member : column ∈ columns) :
    ∃ index, columnPosition columns column.name = some index ∧ columns[index]? = some column := by
  induction columns with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | later
    · subst same
      exact ⟨0, by simp [columnPosition, findPosition, Identifier.sameName], rfl⟩
    · have uniqueTail := (List.nodup_cons.mp unique).2
      have absent := (List.nodup_cons.mp unique).1
      have differs : head.name.sameName column.name = false := by
        simp only [Identifier.sameName, beq_eq_false_iff_ne]
        intro eq
        apply absent
        change head.name.folded ∈ tail.map (·.name.folded)
        rw [eq]
        exact List.mem_map_of_mem later
      obtain ⟨index, lookup, atIndex⟩ := ih uniqueTail later
      refine ⟨index + 1, ?_, by simpa using atIndex⟩
      simp only [columnPosition, findPosition, differs, Bool.false_eq_true, ite_false, Option.map_map]
      simp only [columnPosition] at lookup
      cases found : findPosition (fun c => c.name.sameName column.name) tail with
      | none => simp [found] at lookup
      | some pair => simpa [found] using lookup

/-- The byte-array conversion used by {name}`pragmaText` preserves every byte.
Proof sketch: the loop's reversed accumulator followed by the unread suffix is invariant. -/
private theorem byteArray_toList_data (bytes : ByteArray) : bytes.toList = bytes.data.toList := by
  suffices loop : ∀ index acc, ByteArray.toList.loop bytes index acc =
      acc.reverse ++ bytes.data.toList.drop index by
    simpa [ByteArray.toList] using loop 0 []
  intro index acc
  fun_induction ByteArray.toList.loop bytes index acc with
  | case1 index acc within ih =>
    rw [ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    congr 1
    conv => rhs; rw [List.drop_eq_getElem_cons (by simpa [ByteArray.size_data] using within)]
    congr 1
    simp [ByteArray.get!, within, ByteArray.size_data]
  | case2 index acc past =>
    rw [List.drop_eq_nil_of_le (by simpa [ByteArray.size_data] using Nat.le_of_not_gt past), List.append_nil]

/-- For every two strings, equal pragma text values imply equal strings. Proof sketch:
{name}`pragmaText` preserves UTF-8 bytes, and Lean's UTF-8 representation is injective. -/
theorem pragmaText_injective (first second : String) (same : pragmaText first = pragmaText second) :
    first = second := by
  simp only [pragmaText, Value.text.injEq, byteArray_toList_data, Array.toList_inj,
    String.toUTF8_eq_toByteArray] at same
  apply String.toByteArray_inj.mp
  exact ByteArray.ext same
/-- For every column whose pragma type cell is exactly {lit}`INTEGER`, its comparison
affinity is INTEGER or BLOB. The BLOB case permits an arbitrary catalog column marked
STRICT ANY; no coherence assumption between those metadata fields is required. Proof
sketch: recover the declared type with {Lean.Doc.name}`pragmaText_injective`, then inspect the
STRICT ANY override in {Lean.Doc.name}`CatalogColumn.affinity`. -/
theorem CatalogColumn.affinity_of_integer_pragma (column : CatalogColumn)
    (reported : pragmaText (column.declaredType.getD "") = pragmaText "INTEGER") :
    column.affinity = .integer ∨ column.affinity = .blob := by
  have text := pragmaText_injective _ _ reported
  have declared : column.declaredType = some "INTEGER" := by
    cases found : column.declaredType with
    | none => simp [found] at text
    | some value =>
      have valueEq : value = "INTEGER" := by simpa [found] using text
      simp [valueEq]
  unfold CatalogColumn.affinity
  rw [declared]
  split
  · exact .inr rfl
  · exact .inl rfl
/-- For every table-info reference, argument and rows, the unqualified name
{lit}`type` resolves to the declared-type cell at position 2. Proof sketch: the
pragma's fixed visible column names put only {lit}`type` at that position. -/
theorem tableInfoScope_resolveName_type (reference : Syntax.TableReference) (argument : List UInt8)
    (rows : List (List Value)) :
    (tableInfoScope reference argument rows).resolveName (name! "type") = .found 2 [2] := by
  have position : columnPosition (tableInfoNames.map (fun name =>
      ({ name := Identifier.ofString name, declaredType := none } : CatalogColumn)) ++
      [{ name := Identifier.ofString "arg", declaredType := none },
       { name := Identifier.ofString "schema", declaredType := none }]) (name! "type") = some 2 := by
    decide +kernel
  simp [tableInfoScope, pragmaSource, Scope.place, Scope.resolveName, Scope.depths,
    Scope.resolveAt, Scope.resolveStep, position]

/-- For every table-info reference, argument, rows, quote kind, subquery shapes and
misuse flag, the name {lit}`type` resolves to column 2 with BLOB affinity, which
converts no value. Proof sketch: use {name}`tableInfoScope_resolveName_type` and
read the fixed column's affinity. -/
theorem resolveOperand_tableInfo_type (dqs : Bool) (reference : Syntax.TableReference)
    (argument : List UInt8) (rows : List (List Value)) (quote : Syntax.QuoteKind)
    (shapes : SubqueryShapes) (misuse : Bool) :
    resolveOperand dqs (tableInfoScope reference argument rows) shapes misuse
        (.identifier (name! "type") quote) = .ok (.column 2, some .blob) := by
  simp only [resolveOperand, tableInfoScope_resolveName_type]
  simp [Scope.nameRead, Scope.nameOperand, Scope.affinityAt, tableInfoScope, pragmaSource, Scope.place,
    Scope.argumentCell, Scope.triggerCell, Scope.columns, tableInfoNames,
    CatalogColumn.affinity, affinityOf]

/-- For every table-info reference, argument and rows, its declared-type cell uses
BINARY collation. Proof sketch: the fixed pragma columns declare no collation. -/
theorem tableInfoScope_collation_type (reference : Syntax.TableReference) (argument : List UInt8)
    (rows : List (List Value)) :
    (tableInfoScope reference argument rows).columns[2]?.map (·.collation) = some Collation.binary := by
  simp [tableInfoScope, pragmaSource, Scope.place, tableInfoNames, Scope.columns]

end Belay.Sqlite.Model
