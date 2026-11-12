import Belay.Sqlite.Model.Queries.Preparation.ResolveNamesBelow

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every name, columns and rowid flag, the scope of one table ends below the number of its columns ({name}`Scope.Bounded`). Proof sketch: the only source has offset zero.  -/
theorem Scope.single_bounded (name : Identifier) (columns : List CatalogColumn) (hasRowid : Bool) :
    (Scope.single name columns hasRowid).Bounded columns.length := by
  intro source member
  simp only [Scope.single, List.mem_singleton] at member
  subst member
  simp

end Belay.Sqlite.Model
