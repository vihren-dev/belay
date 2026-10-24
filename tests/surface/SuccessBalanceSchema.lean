import SuccessBalanceObservation

/-! Schema part of the corrected balance example, compiled by the surface success test. -/

set_option doc.verso true
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace BalanceExample

/-- For every context, row and byte list, the name predicate is true exactly when field 1
is that text value. -/
theorem name_eval (context : Resolved.EvalContext) (row : List Value) (bytes : List UInt8) :
    Resolved.truthy ((nameResolved bytes).eval context row) = true ↔ row[1]?.getD .null = .text bytes := by
  simp [sql_simp, nameResolved, Resolved.comparisonOperands, Value.isNull, Comparison.holds]
  intro named
  rw [named]

/-- For every context and row, the typed predicate is true exactly when field 1 is cents
and field 2 is the pragma text INTEGER. -/
theorem typed_eval (context : Resolved.EvalContext) (row : List Value) :
    Resolved.truthy (typedResolved.eval context row) = true ↔
      row[1]?.getD .null = .text (bytes! "cents") ∧ row[2]?.getD .null = pragmaText "INTEGER" := by
  have typeEq : Resolved.truthy ((Resolved.Expr.compare .eq (some .blob) (.column 2)
      (.literal (.text (bytes! "INTEGER"))) .binary).eval context row) = true ↔
      row[2]?.getD .null = pragmaText "INTEGER" := by
    have integerText : pragmaText "INTEGER" = .text (bytes! "INTEGER") := by decide +kernel
    rw [integerText]
    simp [sql_simp, Resolved.comparisonOperands, Value.isNull, Comparison.holds]
    intro named
    rw [named]
  simp only [typedResolved, Resolved.Expr.eval_and, Resolved.truthy_and, Bool.and_eq_true, name_eval, typeEq]

/-- For every context and catalog table, nonempty account and typed-cents results supply
an account column and a cents column whose reported declared type is INTEGER.
Proof sketch: take a retained row from each result and use the table-info row membership laws. -/
theorem metadata_columns (context : Resolved.EvalContext) (table : CatalogTable)
    (account : filteredOnes context (nameResolved (bytes! "account")) (table.infoRows.map (· ++ [.text (bytes! "ledger"), .null])) ≠ [])
    (typed : filteredOnes context typedResolved (table.infoRows.map (· ++ [.text (bytes! "ledger"), .null])) ≠ []) :
    (∃ column ∈ table.columns, column.name.bytes = bytes! "account") ∧
    (∃ column ∈ table.columns, column.name.bytes = bytes! "cents" ∧
      pragmaText (column.declaredType.getD "") = pragmaText "INTEGER") := by
  constructor
  · obtain ⟨row, member⟩ := List.exists_mem_of_ne_nil _ account
    obtain ⟨row, kept, rfl⟩ := List.mem_map.mp member
    obtain ⟨inside, yes⟩ := List.mem_filter.mp kept
    have named := (name_eval context row _).mp yes
    obtain ⟨column, member, generated, named⟩ := (table.exists_pragmaRow_name (bytes! "ledger")
      (fun value => value = .text (bytes! "account"))).mp ⟨row, inside, named⟩
    exact ⟨column, member, Value.text.inj named⟩
  · obtain ⟨row, member⟩ := List.exists_mem_of_ne_nil _ typed
    obtain ⟨row, kept, rfl⟩ := List.mem_map.mp member
    obtain ⟨inside, yes⟩ := List.mem_filter.mp kept
    have typed := (typed_eval context row).mp yes
    obtain ⟨entry, member, generated, typed⟩ := (table.exists_pragmaRow_metadata (bytes! "ledger")
      (fun name type _ _ => name = .text (bytes! "cents") ∧ type = pragmaText "INTEGER")).mp
      ⟨row, inside, typed⟩
    exact ⟨entry.1, List.mem_of_mem_zipIdx_fst member, Value.text.inj typed.1, typed.2⟩

/-- For every database with the ledger, cents column and unshadowed pragma, a true guard
supplies an account column and shows that the cents affinity is INTEGER or BLOB.
Proof sketch: metadata witnesses identify the unique named columns. The BLOB branch keeps
the valid-catalog STRICT ANY override admitted by the model. -/
theorem guard_schema (db : Database) (position index : Nat) (table : CatalogTable) (cell : CatalogColumn)
    (found : db.raw.catalog.findTable ledgerRef.table = some (position, table))
    (notTable : db.raw.catalog.findTable pragmaRef.table = none)
    (column : columnPosition table.columns (name! "cents") = some index)
    (atIndex : table.columns[index]? = some cell) (holds : Holds balanceGuard db) :
    (∃ account, columnPosition table.columns (name! "account") = some account) ∧
      (cell.affinity = .integer ∨ cell.affinity = .blob) := by
  obtain ⟨context, observed⟩ := guard_holds db position index table cell found notTable column atIndex
  have facts := observed.mp holds
  have metadata := metadata_columns context table facts.2.2.1 facts.2.2.2
  have supported := db.valid.admitted.catalogSupported.tableSupported (Catalog.tableAt_of_findTable found)
  have unique := ((CatalogTable.supported_iff _ table).mp supported).2.2.1
  obtain ⟨accountCell, accountMember, accountName⟩ := metadata.1
  obtain ⟨account, accountLookup, accountAt⟩ := column_lookup_of_member table.columns accountCell unique accountMember
  have accountNamed : accountCell.name = name! "account" := congrArg Identifier.mk accountName
  rw [accountNamed] at accountLookup
  obtain ⟨typedCell, typedMember, typedName, integerType⟩ := metadata.2
  obtain ⟨cents, centsLookup, centsAt⟩ := column_lookup_of_member table.columns typedCell unique typedMember
  have centsNamed : typedCell.name = name! "cents" := congrArg Identifier.mk typedName
  rw [centsNamed, column] at centsLookup
  have sameIndex : index = cents := Option.some.inj centsLookup
  subst cents
  rw [atIndex] at centsAt
  have sameCell : cell = typedCell := Option.some.inj centsAt
  subst typedCell
  exact ⟨⟨account, accountLookup⟩, cell.affinity_of_integer_pragma integerType⟩

/-- For every database with the ledger, cents column and unshadowed pragma, a true guard
makes direct NOT BETWEEN false on every source cell and gives fewer than one million rows.
Proof sketch: an empty bad-range result excludes every matching cell. Stored-form validity
removes numeric affinity conversion; the BLOB affinity branch already compares cells directly. -/
theorem guard_bounds (db : Database) (position index : Nat) (table : CatalogTable) (cell : CatalogColumn)
    (found : db.raw.catalog.findTable ledgerRef.table = some (position, table))
    (notTable : db.raw.catalog.findTable pragmaRef.table = none)
    (column : columnPosition table.columns (name! "cents") = some index)
    (atIndex : table.columns[index]? = some cell) (holds : Holds balanceGuard db) :
    (∀ row ∈ Resolved.sourceRows {shape := table, rows := db.raw.rows.getD position []},
      Resolved.truthy ((Comparison.ge.apply (row[index]?.getD .null) (.integer (-1000000000000)) cell.collation).and
        (Comparison.le.apply (row[index]?.getD .null) (.integer 1000000000000) cell.collation)).not = false) ∧
    (db.raw.rows.getD position []).length < 1000000 := by
  obtain ⟨context, observed⟩ := guard_holds db position index table cell found notTable column atIndex
  have facts := observed.mp holds
  have affinity := (guard_schema db position index table cell found notTable column atIndex holds).2
  constructor
  · intro row member
    have empty : ((Resolved.sourceRows {shape := table, rows := db.raw.rows.getD position []}).filter
        (fun row => Resolved.truthy ((rangeResolved index cell).eval context row))) = [] :=
      by simpa [filteredOnes] using facts.1
    have never := List.filter_eq_nil_iff.mp empty row member
    have stored : LiteralData.storedForm cell.affinity (row[index]?.getD .null) = true := by
      obtain ⟨storedRow, scanned, rfl⟩ := List.mem_map.mp member
      have member := (Table.scanRows_perm {shape := table, rows := db.raw.rows.getD position []}).mem_iff.mp scanned
      have stored := db.valid.admitted.rowsStored position _ (db.raw.table_of_findTable _ _ _ found) storedRow member
      simpa [List.getD_eq_getElem?_getD] using stored.storedForm_getD atIndex
    rcases affinity with integer | blob
    · rw [integer] at stored
      have fixed := Resolved.numericOperand_of_stored
        (by decide : Affinity.integer ≠ .text ∧ Affinity.integer ≠ .blob) stored
      simp only [rangeResolved, Resolved.Expr.eval_not, Resolved.Expr.eval_and, Resolved.Expr.eval_compare,
        Resolved.Expr.eval_column, Resolved.Expr.eval_literal, integer, Resolved.comparisonOperands,
        List.getD_eq_getElem?_getD, fixed] at never
      simpa [Resolved.numericOperand] using never
    · simpa [rangeResolved, Resolved.Expr.eval_not, Resolved.Expr.eval_and, Resolved.Expr.eval_compare,
        Resolved.Expr.eval_column, Resolved.Expr.eval_literal, blob, Resolved.comparisonOperands] using never
  · have length : (Resolved.sourceRows {shape := table, rows := db.raw.rows.getD position []}).length =
        (db.raw.rows.getD position []).length := by
      simp only [Resolved.sourceRows, List.length_map]
      exact (Table.scanRows_perm _).length_eq
    simpa only [length] using facts.2.1

end BalanceExample
