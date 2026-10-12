import Generated

/-! A checked refutation identifies the unfulfilled standing catalog requirement. -/
namespace Proofs

/-- The required invoice.note column is absent from the generated resulting catalog. -/
theorem migrationViolated : ¬Generated.expected := by
  apply SqliteVerifier.violates_required_catalog (successRequired := rfl)
  show ¬(Generated.nextCatalog.columnsOf "invoices" =
    some [{ name := "amount", declaredType := some "INTEGER" }, { name := "note", declaredType := some "TEXT" }])
  decide +kernel

end Proofs
