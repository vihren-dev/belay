import Belay

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

namespace CompiledSelectCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open scoped Belay.Sqlite.LastOutput

/-- Two input rows give two copies of a constant projection. -/
private def items : Database := db! r"CREATE TABLE items (id INTEGER); INSERT INTO items VALUES (1), (2);"

/-- Project the supplied binding once per qualifying row. -/
private def byId (value : Value) : Script := sql r"SELECT ?1 FROM items WHERE id" value

/-- An extra conjunct accepts every qualifying row. -/
private def whereTrue (value : Value) : Script := sql r"SELECT ?1 FROM items WHERE id AND 1" value

/-- Check both SELECT compilation and the residual goal of {name}`LastOutputPlan.sameLastOn_iff`.
For every binding, the two SQL spellings return one copy per qualifying row on any matching database.
Proof sketch: compile each script independently. The remaining bag equality drops an always-true filter. -/
theorem equivalent (value : Value) : byId value ~ whereTrue value on items := by
  apply (LastOutputPlan.sameLastOn_iff
    (((byId value).compileLastOutput? items).get (by rfl)).property
    (((whereTrue value).compileLastOutput? items).get (by rfl)).property).mpr
  intro db _ env _
  apply (LastOutputPlan.rowBag_eq_iff _ _).mpr
  apply List.Perm.map
  apply List.Perm.of_eq
  apply List.filter_congr
  intro row _
  let ctx := Resolved.EvalContext.bound [value]
  let idColumn := Resolved.Expr.column 0
  change Resolved.truthy (idColumn.eval ctx row) =
    Resolved.truthy ((idColumn.and (.literal (.integer 1))).eval ctx row)
  simp only [Resolved.Expr.eval_and, Resolved.truthy_and, Resolved.Expr.eval_literal,
    show Resolved.truthy (.integer 1) = true from rfl, Bool.and_true]

/-- Check that the compiler preserves the bound operand and duplicate outputs on the
two-row fixture. A missing or ignored binding would project NULL instead of seven. -/
theorem bound_output :
    ((((byId (.integer 7)).compileLastOutput? items).get (by rfl)).val items Env.newConnection).1 =
      some (.rows [[.integer 7], [.integer 7]]) := by decide +kernel

/-- The first compiler case declines sequences and SELECTs with ordering. -/
theorem unsupported :
    (((byId .null) ++ (whereTrue .null)).compileLastOutput? items).isNone = true ∧
    ((sql r"SELECT id FROM items ORDER BY id").compileLastOutput? items).isNone = true := by
  exact ⟨rfl, rfl⟩

#print axioms equivalent
#print axioms bound_output
#print axioms unsupported

end CompiledSelectCases
