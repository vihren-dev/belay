import Belay.Sqlite.ParseCommand
import Belay.Sqlite.Translation
import Belay.Sqlite.Values
import Belay.Sqlite.Database
import Belay.Sqlite.Script
import Belay.Sqlite.SqlTerm
import Belay.Sqlite.SqlDiagnostics
import Belay.Sqlite.EvalDatabase
import Belay.Sqlite.SqlBang
import Belay.Sqlite.Run
import Belay.Sqlite.RunLaws

/-! The SQLite surface. It reads SQL text while a Lean file elaborates, with the SQLite parser
library in the Lean process, and translates the parse tree to the model's statement syntax with
the source range of each node ({lit}`Belay.Sqlite.Translation` of the text package below the
surface, ADR 0016, D2, amended). -/
