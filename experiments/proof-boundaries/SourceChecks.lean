import SourceEndpoints

set_option doc.verso true

/-! Boundary checks for source agreement: missing tables, shape, and pragma reads. -/

namespace ProofBoundaries

open Belay.Sqlite.Model Belay.Sqlite.Model.Resolved

/-- Missing and present initial tables do not agree, even if the present table has no
rows. Proof sketch: their optional lookups have different constructors. -/
theorem initial_presence_matters (first second database : Database) (position : Nat) (table : Table)
    (found : database.table position = some table) :
    ¬SourceAgrees first second none (some database) (.initialTable position) := by
  simp [SourceAgrees, found]

/-- Agreement retains table shape as well as rows. Proof sketch: equality of the
successful optional lookups implies table equality, hence equality of their shapes. -/
theorem table_shape_retained (first second : Database) (before after : Option Database)
    (position : Nat) (left right : Table)
    (foundLeft : first.table position = some left) (foundRight : second.table position = some right)
    (agree : SourceAgrees first second before after (.table position)) : left.shape = right.shape := by
  simp only [SourceAgrees, foundLeft, foundRight, Option.some.injEq] at agree
  exact congrArg Table.shape agree

/-- Unlike a check pragma, fixed pragma rows agree for arbitrary current databases.
This is accepted by source agreement although the existing current-read test excludes it. -/
theorem fixed_pragma_agrees (first second : Database) (before after : Option Database)
    (width : Nat) (rows : List (List Value)) :
    SourceAgrees first second before after (.pragma (.fixed width rows)) ∧
      (Source.pragma (.fixed width rows)).readsCurrent = true := ⟨rfl, rfl⟩

/-- A query over only a fixed pragma is independent of both database origins. Proof sketch:
the sole source agrees by reduction, and there are no nested queries. This is a genuine
new application which the old current-read exclusion cannot prove directly. -/
theorem fixed_pragma_possible (query : Query) (width : Nat) (rows : List (List Value))
    (sources : query.sources = [{ kind := .inner, source := .pragma (.fixed width rows), condition := none }])
    (clock : Int) (counters : Counters) (parameters : List Value)
    (first second : Database) (before after : Option Database) :
    query.possibleOn clock counters parameters first [] before =
      query.possibleOn clock counters parameters second [] after := by
  apply possibleOn_agrees query clock counters parameters first second [] before after
  · intro join member
    rw [sources] at member
    simp only [List.mem_singleton] at member
    subst join
    rfl
  · simp

#print axioms initial_presence_matters
#print axioms table_shape_retained
#print axioms fixed_pragma_possible

end ProofBoundaries
