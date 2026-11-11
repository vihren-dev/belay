import Belay.Sqlite.Model.Queries.Preparation.ResolveTableShaped
import Belay.Sqlite.Model.Queries.Evaluation.ResolveCallsBelow

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every columns, names and positions: if {name}`keyPositions` gives positions, there is one
position for each name, and each is below the number of columns. Proof sketch: induction over the
names; a found column is below the length ({name}`columnPosition_lt`). -/
theorem keyPositions_cases {columns : List CatalogColumn} :
    ∀ {names : List Identifier} {positions : List Nat}, keyPositions columns names = .ok positions →
      positions.length = names.length ∧ ∀ position ∈ positions, position < columns.length
  | [], positions, ok => by
    simp only [keyPositions, Except.ok.injEq] at ok; subst ok; simp
  | name :: rest, positions, ok => by
    simp only [keyPositions] at ok
    cases found : columnPosition columns name with
    | none => simp [found] at ok
    | some position =>
      simp only [found] at ok
      cases hrest : keyPositions columns rest with
      | error _ => simp [hrest, Except.map] at ok
      | ok tail =>
        simp only [hrest, Except.map, Except.ok.injEq] at ok
        subst ok
        obtain ⟨lengths, below⟩ := keyPositions_cases hrest
        refine ⟨by simp [lengths], fun place member => ?_⟩
        rcases List.mem_cons.mp member with rfl | inner
        · exact columnPosition_lt found
        · exact below place inner

end Belay.Sqlite.Model
