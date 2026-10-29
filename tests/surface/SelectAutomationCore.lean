import Belay

set_option doc.verso true
set_option sql.check false

/-! Bounded experiments for ADR 0027. These facts concern the existing pure SELECT
functions. Execution, faults and all permitted outputs are separate obligations. -/

namespace SelectAutomation
open Belay.Sqlite
open Belay.Sqlite.Model.Resolved

/-- A column projection with an optional SQL condition, for the pure phase experiments. -/
def projection (condition : Option Expr := none) : Query :=
  Query.simple [] condition [.scalar (.column 0)] ["value"]

/-- For every source list and condition, the projection has exactly one result row per
retained source row, including duplicate and empty rows. Proof sketch: the existing length law. -/
theorem collection_count (context : EvalContext) (rows : List (List Value)) (condition : Option Expr) :
    ((projection condition).results context rows).length =
      (filtered context (projection condition) rows).length :=
  (Query.simple_isSimple _ _ _ _).results_length context rows

/-- The pure projection retains two equal source rows; projection does not imply DISTINCT. -/
theorem duplicates_remain :
    (projection none).results (.bound []) [[.integer 7], [.integer 7]] =
      [[.integer 7], [.integer 7]] := by decide +kernel

/-- Every projected row comes from a source row for which the exact SQL truth test passed.
No condition on the input list is needed, and an empty result requires no row witness.
Proof sketch: the simple-result equation, followed by membership in map and filter. -/
theorem where_fact (context : EvalContext) (condition : Expr) (rows : List (List Value))
    (row : List Value) (member : row ∈ (projection (some condition)).results context rows) :
    ∃ source ∈ rows, truthy (condition.eval context source) = true ∧
      row = [source.getD 0 .null] := by
  simp only [projection] at member
  rw [(Query.simple_isSimple _ _ _ _).results_eq] at member
  obtain ⟨source, kept, rfl⟩ := List.mem_map.mp member
  obtain ⟨original, accepted⟩ := (mem_filtered context _ rows source).mp kept
  exact ⟨source, original, accepted, rfl⟩

/-- For every source list, WHERE IS NOT NULL establishes non-NULL in the projected
cell without a schema assumption. No source row or cell existence is assumed.
Proof sketch: the retained SQL truth test contradicts a NULL projected value. -/
theorem where_nonnull (context : EvalContext) (rows : List (List Value))
    (row : List Value)
    (member : row ∈ (projection (some (.isNull (.column 0) true))).results context rows) :
    ∃ value, row = [value] ∧ value ≠ .null := by
  obtain ⟨source, _, accepted, rfl⟩ := where_fact context _ rows row member
  refine ⟨source.getD 0 .null, rfl, ?_⟩
  intro isNull
  rw [Expr.eval_isNull, Expr.eval_column, isNull] at accepted
  cases accepted

/-- A count and a sum over the same source, for checking the empty-group boundary. -/
def aggregatePair : Query :=
  { (projection none) with
    aggregate := true
    columns := [.aggregate .countRows, .aggregate (.sum (.column 0))]
    names := ["count", "sum"] }

/-- An ungrouped aggregate emits a row for an empty source: count zero and NULL sum. -/
theorem aggregate_empty : aggregatePair.results (.bound []) [] = [[.integer 0, .null]] := by
  decide +kernel

/-- A one-row window with no ordering term, which can choose either source row. -/
def chooseOne : Query := { projection none with limit := some 1 }

/-- The representative pure result is only one of the two results permitted by the window. -/
theorem window_alternatives :
    chooseOne.results (.bound []) [[.integer 1], [.integer 2]] = [[.integer 1]] ∧
    chooseOne.possibleResults (.bound []) [[.integer 1], [.integer 2]] =
      [[[.integer 1]], [[.integer 2]]] := by decide +kernel

/-- Every permitted window result has one non-NULL cell, but they do not all equal the
representative result. This compares whole collections and every alternative. -/
theorem every_window_result :
    (∀ rows ∈ chooseOne.possibleResults (.bound []) [[.integer 1], [.integer 2]],
      rows.length = 1 ∧ ∀ row ∈ rows, ∀ value ∈ row, value ≠ .null) ∧
    ¬ (∀ rows ∈ chooseOne.possibleResults (.bound []) [[.integer 1], [.integer 2]],
      rows = chooseOne.results (.bound []) [[.integer 1], [.integer 2]]) := by
  decide +kernel

#print axioms collection_count
#print axioms duplicates_remain
#print axioms where_fact
#print axioms where_nonnull
#print axioms aggregate_empty
#print axioms window_alternatives
#print axioms every_window_result

end SelectAutomation
