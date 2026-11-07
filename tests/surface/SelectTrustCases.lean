import SelectProcedureCases

set_option doc.verso true

/-! A fixture module of {lit}`tests/surface_select_procedure_test.py`: the trust boundaries of
{lit}`sql_select` (B03, B07). A false precondition proves a triple, but such a triple says nothing about
any run, unlike the A01 theorem, whose catalog premise has an empty and a populated witness. A false
claim that a valid witness refutes does not close. A rule that is not proved cannot give a proof that the
axiom audit accepts: the attribute refuses an axiom, and a proof that uses a rule proved with
{lit}`sorry` depends on {lit}`sorryAx`. -/

namespace SelectTrustCases
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database
open SelectProjectionCases

/-- A vacuous triple: from every context at which {lean}`False` holds, the motivating query ends with an
empty result. No context satisfies the precondition, so the triple holds logically and says nothing
about a run; the A01 theorem {name}`customer_present` has no such precondition, and its catalog premise
holds on {name}`invoices` and on {name}`shop` ({name}`populated_witness`). -/
theorem vacuous_triple :
    ⦃fun _ : ExecutionContext => ⌜False⌝⦄ query customerOfFirst customerOfFirst_one
    ⦃⇓ result _ => ⌜result = .ok []⌝⦄ := by
  mintro ⌜impossible⌝
  exact impossible.elim

/-- The claim that the motivating query returns an empty result on every database with the catalog of
{name}`invoices` and in every environment is false: {name}`shop` has the catalog, and the query returns
a row there. -/
theorem empty_claim_refuted :
    ¬ ∀ (db : Database) (env : Env), db.HasCatalog invoices →
      (db.run (query customerOfFirst customerOfFirst_one) env).returnsResult (· = []) := by
  intro claim
  have refuted := claim shop Env.default (by decide +kernel)
  revert refuted
  decide +kernel

/-- warning: sql_select stopped in the result phase: the facts that the rules give do not prove the goal. -/
#guard_msgs (warning, substring := true) in
/-- The claim of the vacuous triple without its precondition: for every database with the catalog of
{name}`invoices`, the motivating query returns an empty result. The claim is false
({name}`empty_claim_refuted`), and the procedure leaves it open. -/
example (db : Database) (env : Env) (schema : db.HasCatalog invoices) :
    (db.run (query customerOfFirst customerOfFirst_one) env).returnsResult (· = []) := by
  sql_select [schema]
  sorry

/-- A false source rule, stated as an axiom: every scanned row of the first table of every database is
empty. -/
axiom empty_row_axiom {db : Database} {row : List Value} (member : row ∈ db.scanAt 0) : row = []

/-- error: sql_select_rule: `SelectTrustCases.empty_row_axiom` is not a theorem. Register a proved theorem. -/
#guard_msgs in
attribute [sql_select_rule source] empty_row_axiom

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- The same false source rule, as a theorem proved with {lit}`sorry`. -/
theorem empty_row {db : Database} {row : List Value} (member : row ∈ db.scanAt 0) : row = [] := by
  sorry

/-- The claim that each scanned row of the first table of every database is empty is false: the scanned rows of the first table of {name}`shop` are not
empty. -/
theorem empty_rows_refuted : ¬ ∀ (db : Database) (row : List Value), row ∈ db.scanAt 0 → row = [] := by
  intro claim
  have first := claim shop
  revert first
  decide +kernel

section
attribute [local sql_select_rule source] empty_row

/-- For every database, each scanned row of its first table is empty. The rule {name}`empty_row` closes
the goal, so the proof depends on {lit}`sorryAx`, which the axiom audit rejects. The claim is false
({name}`empty_rows_refuted`). -/
theorem empty_rows (db : Database) (row : List Value) (member : row ∈ db.scanAt 0) : row = [] := by
  sql_select

end

/-- info: 'SelectTrustCases.empty_rows' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms empty_rows

end SelectTrustCases

#print axioms SelectTrustCases.vacuous_triple
#print axioms SelectTrustCases.empty_claim_refuted
#print axioms SelectTrustCases.empty_rows_refuted
