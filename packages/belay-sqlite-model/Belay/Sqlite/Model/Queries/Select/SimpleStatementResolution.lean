import Belay.Sqlite.Model.Queries.Select.SimpleSourceResolution

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- A {lit}`SELECT` without {lit}`FROM` and without joins resolves to no source and no scope, for
any catalog. Proof sketch: unfold the resolver; there is no table to look up. -/
theorem resolveSources_none (catalog : Catalog) :
    resolveSources catalog none [] = .ok ([], []) := by
  simp [resolveSources, resolveSourcesTraced, traced_drop]

end Belay.Sqlite.Model
