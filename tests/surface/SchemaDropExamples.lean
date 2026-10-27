import SchemaStepLaws

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! A fixture module of {lit}`tests/surface_schema_script_test.py`: the laws of DROP TABLE (ADR 0017, S6, task
{lit}`20261027-schema-script-laws`) on the database of {lit}`SchemaStepLaws`. With foreign keys off the frame law keeps
the child, found by its name at the moved position. With foreign keys on the cascade empties the child, so the frame
law needs its premise, and the success law names the key run. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace SchemaDropExamples
open SchemaStepLaws


/-- The statement that drops the parent. -/
def dropParent : Syntax.Statement := .dropTable (name! "p") false

/-- The script text of the drop is the statement {lean}`dropParent`. -/
theorem dropParent_parses : statementOf (sql r"DROP TABLE p;") = dropParent := rfl

/-- With foreign keys off, the drop of the parent resolves to a drop of position 0 without rules. -/
theorem drop_resolves_plain : resolvesTo start dropParent (.drop [0] none) = true := by decide +kernel

/-- With foreign keys on, the same drop resolves to a drop with rules. -/
theorem drop_resolves_with_rules : resolvesShape enforcing dropParent (.dropWithRules [0]) = true := by
  decide +kernel

/-- Frame law of DROP TABLE with foreign keys off: the child is found by its name at position 0 after the drop of
the parent that stood before it, with the rows that it had at position 1. Proof sketch:
{name}`runScriptStep_dropTable_frame`; the kernel shows that the step continues and that the child had its three
rows at position 1. -/
theorem drop_off_keeps_the_child : ∀ output next others, stepOf start dropParent = .continued output next others →
    foundRows next.state.database (name! "c") =
      some (0, [(10, [.integer 10, .integer 1, .text [97]]), (11, [.integer 11, .integer 2, .text [98]]),
        (12, [.integer 12, .integer 2, .text [99]])]) := by
  intro output next others step
  obtain ⟨after, found⟩ := resolvesTo_sound drop_resolves_plain
  obtain ⟨table, present⟩ := tableNamed_exists (database := start.state.database) (name := name! "c") (position := 1)
    (by decide +kernel)
  have kept := runScriptStep_dropTable_frame (connection := start) (dropped := name! "p") (ifExists := false) rfl found
    step (other := name! "c") (by decide +kernel) present
  have rows := start_rows.2
  unfold foundRows at rows ⊢
  rw [present] at rows
  have moved : keptBelow [0] 1 = 0 := by decide +kernel
  rw [kept, moved]
  simpa using rows

/-- Success law of DROP TABLE with foreign keys off: the database after is the database without the dropped
table and its rows. Proof sketch: {name}`runScriptStep_drop_plain`. -/
theorem drop_off_removes_the_parent : ∀ output next others, stepOf start dropParent = .continued output next others →
    output.isError = false ∧ others = [] ∧ foundRows next.state.database (name! "p") = none := by
  intro output next others step
  obtain ⟨after, found⟩ := resolvesTo_sound drop_resolves_plain
  obtain ⟨noError, single, nextEq⟩ := runScriptStep_drop_plain found step
  refine ⟨noError, single, ?_⟩
  rw [nextEq]
  decide +kernel

-- With foreign keys on

/-- Premise of the frame law of DROP TABLE: with foreign keys on, dropping the parent deletes the rows of the child
by the cascade. The child is found by its name at position 0 after the drop, with no rows, so the frame law does not
hold without the premise that foreign keys are off. Proof sketch: kernel evaluation of the step. -/
theorem drop_on_cascades_into_the_child : ∀ output next others, stepOf enforcing dropParent = .continued output next others →
    foundRows next.state.database (name! "c") = some (0, []) := by
  intro output next others step
  have kernel : (afterStep enforcing dropParent).map (fun after => foundRows after.state.database (name! "c")) =
      some (some (0, [])) := by decide +kernel
  rw [afterStep_of_continued step] at kernel
  simpa using kernel

/-- The success law of DROP TABLE with foreign keys on is the law of the key run: the catalog after is the catalog
without the dropped objects. The rows depend on the actions of the keys, which is why the law names the key run and
not the rows. Proof sketch: {name}`runScriptStep_drop_keys` with the resolution of the drop with rules. -/
theorem drop_on_removes_the_parent_from_the_catalog : ∀ output next others,
    stepOf enforcing dropParent = .continued output next others → output.isError = false →
      next.state.database.catalog = enforcing.state.database.catalog.drop [0] := by
  intro output next others step noError
  obtain ⟨rules, after, found⟩ := resolvesShape_dropWithRules (statement := dropParent) (connection := enforcing) (positions := [0]) drop_resolves_with_rules
  obtain ⟨_, _, _, catalogEq, _⟩ := runScriptStep_drop_keys found step noError
  exact catalogEq

#print axioms drop_off_keeps_the_child
#print axioms drop_off_removes_the_parent
#print axioms drop_on_cascades_into_the_child
#print axioms drop_on_removes_the_parent_from_the_catalog


end SchemaDropExamples
