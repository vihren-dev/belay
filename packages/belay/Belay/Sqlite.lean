import Belay.Sqlite.ParseCommand
import Belay.Sqlite.Translation

/-! The SQLite surface. It reads SQL text while a Lean file elaborates, with the SQLite parser
library in the Lean process, and translates the parse tree to the model's statement syntax with
the source range of each node ({lit}`Belay.Sqlite.Translation`, a prototype of ADR 0017, S1). -/
