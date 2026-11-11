import Belay.Sqlite.Model.Schema.Dispatch.StatementStep

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every run that {name}`StatementRun.withKeys` builds, the run has no alternative. Proof sketch:
the cases of the optional run of the keys build a run with the default alternatives. -/
theorem StatementRun.withKeys_alternatives (effect : Effect) (ready : Bool) (counts : Counts) (keys : Option KeyRun) :
    (StatementRun.withKeys effect ready counts keys).alternatives = [] := by
  cases keys <;> rfl

end Belay.Sqlite.Model
