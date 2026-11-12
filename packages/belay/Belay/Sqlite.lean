import Belay.Sqlite.Frontend.Grammar.ParseCommand
import Belay.Sqlite.Tooling.SqlCommands.SqlBang
import Belay.Sqlite.Tooling.SqlCommands.SqlModule
import Belay.Sqlite.Tooling.Counterexamples.ValueDisplay
import Belay.Sqlite.Programs.Reasoning.ExecutionEquivalenceBind
import Belay.Sqlite.Programs.StatementRunLaws.DerivedColumnQueries
import Belay.Sqlite.Programs.StatementRunLaws.DerivedColumnSchema
import Belay.Sqlite.Programs.Scripts.ContextObservationBridge
import Belay.Sqlite.Programs.Claims.FreshFromNotation
import Belay.Sqlite.Programs.StatementRunLaws.PlainWriteFrames
import Belay.Sqlite.Programs.Claims.SendStatementsInvariant
import Belay.Sqlite.Programs.Claims.SendStatementsSuccess
import Belay.Sqlite.Tooling.Tests.SqlAuto
import Belay.Sqlite.Programs.Scripts.SendSuccessIfOk
import Belay.Sqlite.Programs.Claims.MigrationExplainCommand
import Belay.Sqlite.Programs.Claims.SuccessSyntax
import Belay.Sqlite.Programs.Scripts.CreateIndexSuccess
import Belay.Sqlite.Programs.Claims.SelectErrorBridge
import Belay.Sqlite.Tooling.Counterexamples.SelectCalmExecution
import Belay.Sqlite.Programs.Claims.SelectOverflow
import Belay.Sqlite.Tooling.Counterexamples.SelectContextExecution
import Belay.Sqlite.Tooling.Counterexamples.QueryBridge
import Belay.Sqlite.Tooling.Counterexamples.SqlCommand
import Belay.Sqlite.Programs.StatementRunLaws.NotInQuery
import Belay.Sqlite.Tooling.Counterexamples.SqlCheckCommand
import Belay.Sqlite.Tooling.Counterexamples.SqlRefuteSearch
import Belay.Sqlite.Tooling.Counterexamples.SqlSelectRules
import Belay.Sqlite.Tooling.Counterexamples.SqlAutomatic
import Belay.Sqlite.Tooling.SqlCommands.SqlDocBlock
import Belay.Sqlite.Programs.Reasoning.ApplicationTranslation
import Belay.Sqlite.Programs.Reasoning.ApplicationQuerySimulation
import Belay.Sqlite.Programs.Reasoning.ScopedRowSteps
import Belay.Sqlite.Programs.Reasoning.ApplicationSyntax

/-! The SQLite surface. It reads SQL text while a Lean file elaborates, with the SQLite parser
library in the Lean process, and translates the parse tree to the model's statement syntax with
the source range of each node ({lit}`Belay.Sqlite.Translation` of the text package below the
surface, ADR 0016, D2, amended). -/
