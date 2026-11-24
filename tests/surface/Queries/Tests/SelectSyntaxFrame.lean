import Belay

/-! SELECT syntax supplies the connection and execution frame for the rowid lookup fixtures. -/

namespace Belay.Sqlite
open Model

/-- The original SELECT syntax supplies the frame for both a query and a prepare error. -/
theorem selectFrame {statement : Syntax.Statement} (select : IsSelectStatement statement)
    {clock : Option Clock} {index : Nat} {conn : Connection} {values : List Value} :
    ∀ output next others, runScriptStep runContext clock index conn statement values = .continued output next others →
      others = [] ∧ next = conn := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := select
  exact fun _ _ _ => runScriptStep_select_keeps

end Belay.Sqlite
