import Belay

set_option doc.verso true

/-! The former schema statements of ADR 0033, derived with their original premises. -/

namespace Belay.Sqlite.Model.ReplacedSchema

/-- The deleted law {lit}`runScriptStep_drop_continues`. For every connection, statement and values that resolve to a DROP TABLE without rules, which is the
resolution while foreign-key enforcement is off: the step continues, with no further execution. In plain
words, the model describes a drop that no foreign key can cascade from. Proof sketch: the applicable branch of {name}`runScriptStep_dropPlain_eq` gives the result. -/
theorem runScriptStep_drop_continues {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {positions : List Nat}
    (found : resolveStatement context connection.resolveState statement = .ok (.drop positions none, after)) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] := by
  simp only [runScriptStep_dropPlain_eq found]
  exact ⟨_, _, rfl⟩

/-- The deleted law {lit}`runScriptStep_rewrite_continues`. For every connection, statement and values that resolve to a rewrite of the catalog that keeps the
outline of the catalog ({name}`Catalog.sameOutline`), as a rename does: the step continues, with no further
execution. In plain words, the model describes a rename whose new catalog has the outline of the old one. Proof sketch: the applicable branch of {name}`runScriptStep_rewrite_eq` gives the result. -/
theorem runScriptStep_rewrite_continues {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {renamed : Catalog}
    (found : resolveStatement context connection.resolveState statement = .ok (.rewrite renamed, after))
    (outline : connection.state.database.catalog.sameOutline renamed = true) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] := by
  simp only [runScriptStep_rewrite_eq found, outline, ite_true]
  exact ⟨_, _, rfl⟩

/-- The deleted law {lit}`runScriptStep_drop_ok`. For every connection, statement and values that resolve to a DROP TABLE without rules: the step continues
without further execution, and its output is no error. In plain words, a drop that no foreign key can cascade
from succeeds. Proof sketch: the applicable branch of {name}`runScriptStep_dropPlain_eq` gives the result. -/
theorem runScriptStep_drop_ok {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {positions : List Nat}
    (found : resolveStatement context connection.resolveState statement = .ok (.drop positions none, after)) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] ∧
      output.isError = false := by
  simp only [runScriptStep_dropPlain_eq found]
  exact ⟨_, _, rfl, rfl⟩

/-- The deleted law {lit}`runScriptStep_rewrite_ok_of_outline`. For every connection, statement and values that resolve to a rewrite of the catalog that keeps its outline:
the step continues without further execution, and its output is no error. In plain words, a rename that keeps the
outline of the catalog succeeds. Proof sketch: the applicable branch of {name}`runScriptStep_rewrite_eq` gives the result. -/
theorem runScriptStep_rewrite_ok_of_outline {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {renamed : Catalog}
    (found : resolveStatement context connection.resolveState statement = .ok (.rewrite renamed, after))
    (outline : connection.state.database.catalog.sameOutline renamed = true) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] ∧
      output.isError = false := by
  simp only [runScriptStep_rewrite_eq found, outline, ite_true]
  exact ⟨_, _, rfl, rfl⟩

/-- The deleted law {lit}`runScriptStep_rewrite_ok`. On every valid database, if resolution gives a catalog rewrite, its step continues once
with a successful output. Proof sketch: the applicable branch of {name}`runScriptStep_rewrite_eq` gives the result. -/
theorem runScriptStep_rewrite_ok {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {renamed : Catalog} {profile : Profile}
    (found : resolveStatement context connection.resolveState statement = .ok (.rewrite renamed, after))
    (valid : connection.state.database.Valid profile) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] ∧
      output.isError = false := by
  simp only [runScriptStep_rewrite_eq found, show _ = true from step_guards_hold found rfl valid, ite_true]
  exact ⟨_, _, rfl, rfl⟩

/-- The deleted law {lit}`runScriptStep_dropColumn_ok`. Every resolved DROP COLUMN on a valid database continues with one successful execution. Proof sketch: the applicable branch of {name}`runScriptStep_dropColumn_eq` gives the result. -/
theorem runScriptStep_dropColumn_ok {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {c : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {pos column : Nat} {stored : Catalog} {profile : Profile}
    (found : resolveStatement context c.resolveState statement = .ok (.dropColumn pos column stored, after))
    (valid : c.state.database.Valid profile) :
    ∃ output next, runScriptStep context clock index c statement parameters = .continued output next [] ∧
      output.isError = false := by
  simp only [runScriptStep_dropColumn_eq found, show _ = true from step_guards_hold found rfl valid, ite_true]
  exact ⟨_, _, rfl, rfl⟩

#print axioms runScriptStep_drop_continues
#print axioms runScriptStep_rewrite_continues
#print axioms runScriptStep_drop_ok
#print axioms runScriptStep_rewrite_ok_of_outline
#print axioms runScriptStep_rewrite_ok
#print axioms runScriptStep_dropColumn_ok

end Belay.Sqlite.Model.ReplacedSchema
