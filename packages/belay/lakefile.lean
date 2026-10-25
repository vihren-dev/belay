import Lake
open Lake DSL System

/-! The surface: the library that users import, {lit}`Belay`, with SQLite under
{lit}`Belay.Sqlite` (ADR 0016, D1). It reads SQL text with the text package below it
({lit}`belaySqliteText`), which calls the SQLite parser library as native code while a file
elaborates, so the surface's modules are precompiled too. The text package's lakefile reads the
parser library's folder from the environment variable {lit}`BELAY_PARSER_LIBRARY`. -/

package belay

require belaySqliteModel from "../belay-sqlite-model"
require belaySqliteText from "../belay-sqlite-text"
require plausible from git "https://github.com/leanprover-community/plausible" @ "118aa17ee84656b8bd727fef7c458ee8c833385c"

/-- The surface library. Its modules are precompiled, so that the interpreter that runs a
file's commands calls the parser library's native code. The library names its modules: a root
{lit}`Belay` would make Lake take every module under {lit}`Belay`, the model's and the text
package's too, as part of this package. -/
@[default_target]
lean_lib Belay where
  roots := #[]
  globs := #[.one `Belay, .one `Belay.Sqlite, .one `Belay.Sqlite.ParseCommand, .one `Belay.Sqlite.Values, .one `Belay.Sqlite.Database,
    .one `Belay.Sqlite.Script, .one `Belay.Sqlite.SqlLiteral, .one `Belay.Sqlite.SqlParameters, .one `Belay.Sqlite.SqlTerm, .one `Belay.Sqlite.SqlDiagnostics, .one `Belay.Sqlite.EvalDatabase,
    .one `Belay.Sqlite.SqlBang, .one `Belay.Sqlite.SqlSourceRecord, .one `Belay.Sqlite.SqlCheckReport, .one `Belay.Sqlite.SqlFileSource, .one `Belay.Sqlite.SqlFileLoad, .one `Belay.Sqlite.SqlFileLexer, .one `Belay.Sqlite.SqlFileLayout, .one `Belay.Sqlite.SqlFileForms, .one `Belay.Sqlite.SqlFileSyntax, .one `Belay.Sqlite.SqlModule, .one `Belay.Sqlite.SqlFileMarkers, .one `Belay.Sqlite.SqlFileDiagnostics,
    .one `Belay.Sqlite.SqlFileTerm, .one `Belay.Sqlite.Run, .one `Belay.Sqlite.Program, .one `Belay.Sqlite.Env, .one `Belay.Sqlite.ValueDisplay,
    .one `Belay.Sqlite.ProgramRun, .one `Belay.Sqlite.ProgramQueries, .one `Belay.Sqlite.ProgramLaws, .one `Belay.Sqlite.ProgramMonadLaws, .one `Belay.Sqlite.ProgramBindLaws, .one `Belay.Sqlite.ExecutionContext, .one `Belay.Sqlite.ExecutionBranches, .one `Belay.Sqlite.ExecutionBranchLaws, .one `Belay.Sqlite.ExecutionBind, .one `Belay.Sqlite.ExecutionWP, .one `Belay.Sqlite.ExecutionStep, .one `Belay.Sqlite.ExecutionWPLaws, .one `Belay.Sqlite.ExecutionSuccess, .one `Belay.Sqlite.ExecutionFresh, .one `Belay.Sqlite.ExecutionEquivalence, .one `Belay.Sqlite.ExecutionEquivalenceLaws, .one `Belay.Sqlite.ExecutionEquivalenceBind, .one `Belay.Sqlite.ExecutionObservations, .one `Belay.Sqlite.ExecutionView, .one `Belay.Sqlite.ExecutionViewProjection, .one `Belay.Sqlite.ExecutionViewLaws, .one `Belay.Sqlite.ExecutionViewBind, .one `Belay.Sqlite.ExecutionViewEquivalence, .one `Belay.Sqlite.ExecutionViewEquivalenceLaws, .one `Belay.Sqlite.ExecutionViewIdentity, .one `Belay.Sqlite.MigrationPattern, .one `Belay.Sqlite.MigrationPatternFresh, .one `Belay.Sqlite.MigrationPatternLaws, .one `Belay.Sqlite.ExecutionViewFrames, .one `Belay.Sqlite.ExecutionViewBindFrames, .one `Belay.Sqlite.ExecutionViewEquivalenceBind, .one `Belay.Sqlite.ExecutionViewObservationBind, .one `Belay.Sqlite.ExecutionViewMonad, .one `Belay.Sqlite.MigrationPatternSuccess, .one `Belay.Sqlite.MigrationPatternQuiet, .one `Belay.Sqlite.MigrationPatternComposition, .one `Belay.Sqlite.MigrationPatternFrames, .one `Belay.Sqlite.SendStatementsBranches, .one `Belay.Sqlite.SingleStatementObservations, .one `Belay.Sqlite.MigrationPatternAfter, .one `Belay.Sqlite.NormalizedFieldExpansion, .one `Belay.Sqlite.MigrationApplicationViews, .one `Belay.Sqlite.MigrationApplicationLaws, .one `Belay.Sqlite.MigrationPatternSyntax, .one `Belay.Sqlite.MigrationExplanation, .one `Belay.Sqlite.MigrationExplainCommand, .one `Belay.Sqlite.ExecutionSpecifications, .one `Belay.Sqlite.Success, .one `Belay.Sqlite.ProgramSuccess, .one `Belay.Sqlite.ScriptSuccess, .one `Belay.Sqlite.SuccessSyntax, .one `Belay.Sqlite.QuerySuccess, .one `Belay.Sqlite.CreateIndexSuccess, .one `Belay.Sqlite.ProgramEnvLaws, .one `Belay.Sqlite.RunLaws, .one `Belay.Sqlite.DbDiagnostics,
    .one `Belay.Sqlite.DbBang, .one `Belay.Sqlite.Queries, .one `Belay.Sqlite.QueryLaws, .one `Belay.Sqlite.QueryBridge, .one `Belay.Sqlite.QueryCases, .one `Belay.Sqlite.SelectOneFrom, .one `Belay.Sqlite.SqlSimp, .one `Belay.Sqlite.SqlSimpLaws, .one `Belay.Sqlite.ExistsQuery, .one `Belay.Sqlite.NotExistsQuery, .one `Belay.Sqlite.SelectOneMayFail, .one `Belay.Sqlite.ExistsMayFail, .one `Belay.Sqlite.ScalarNoFrom, .one `Belay.Sqlite.SelectNoFrom, .one `Belay.Sqlite.CountQuery, .one `Belay.Sqlite.ColumnQuery, .one `Belay.Sqlite.TableInfoQuery, .one `Belay.Sqlite.DuplicateKeyQuery, .one `Belay.Sqlite.AggregateQuery, .one `Belay.Sqlite.UniqueLookupQuery, .one `Belay.Sqlite.SqlCommand]
    ++ #[.one `Belay.Sqlite.CounterexampleCertificate, .one `Belay.Sqlite.CounterexampleWitness,
      .one `Belay.Sqlite.SqlRefute, .one `Belay.Sqlite.SampleValues, .one `Belay.Sqlite.SampleDatabases,
      .one `Belay.Sqlite.SampleShrink, .one `Belay.Sqlite.CounterexampleShrink,
      .one `Belay.Sqlite.SampleHints, .one `Belay.Sqlite.SampleQueryHints, .one `Belay.Sqlite.SampleScriptHints,
      .one `Belay.Sqlite.SqlSource, .one `Belay.Sqlite.ReplayValues, .one `Belay.Sqlite.ReplayDatabaseSql,
      .one `Belay.Sqlite.ReplayEvaluation, .one `Belay.Sqlite.ReplayConstruction, .one `Belay.Sqlite.ReplayScript,
      .one `Belay.Sqlite.SqlEditorSource, .one `Belay.Sqlite.SqlParameterInfo,
      .one `Belay.Sqlite.SqlTableSlots, .one `Belay.Sqlite.SqlStatementContexts, .one `Belay.Sqlite.SqlTableDescription,
      .one `Belay.Sqlite.SqlTableInfo, .one `Belay.Sqlite.SqlTableOrigins, .one `Belay.Sqlite.SqlEditorInfo,
      .one `Belay.Sqlite.SqlOrderWarnings]
    ++ #[.one `Belay.Sqlite.CheckBudget, .one `Belay.Sqlite.CheckData,
      .one `Belay.Sqlite.CheckReplayData, .one `Belay.Sqlite.CheckProof,
      .one `Belay.Sqlite.CheckCandidates, .one `Belay.Sqlite.CheckClaim,
      .one `Belay.Sqlite.CheckRandom, .one `Belay.Sqlite.CheckSamples,
      .one `Belay.Sqlite.CheckReplay, .one `Belay.Sqlite.CheckOperation,
      .one `Belay.Sqlite.CheckInputSyntax, .one `Belay.Sqlite.CheckDeclarations, .one `Belay.Sqlite.CheckExample, .one `Belay.Sqlite.SqlAutomatic,
      .one `Belay.Sqlite.CheckOptions, .one `Belay.Sqlite.CheckInputs, .one `Belay.Sqlite.CheckDisplay,
      .one `Belay.Sqlite.SqlCheckCommand, .one `Belay.Sqlite.SqlRefuteSearch]
    ++ #[.one `Belay.Sqlite.SqlDocObservation, .one `Belay.Sqlite.SqlDocCheck,
      .one `Belay.Sqlite.SqlDocComments, .one `Belay.Sqlite.SqlDocSource, .one `Belay.Sqlite.SqlDocBindings,
      .one `Belay.Sqlite.SqlDocClosed, .one `Belay.Sqlite.SqlDocHeader, .one `Belay.Sqlite.SqlDocReport,
      .one `Belay.Sqlite.SqlDocInputs, .one `Belay.Sqlite.SqlDocFailure, .one `Belay.Sqlite.SqlDocBlock,
      .one `Belay.Sqlite.SqlDocGuide]
  precompileModules := true

/-- The SQL-file checker (ADR 0017, S7), run as {lit}`lake exe belay-sql-check`. It is the only
module that imports Lake, so {lit}`import Belay` does not depend on the build system. It inspects
the compiled libraries of the package that runs it and builds none of them. -/
lean_exe «belay-sql-check» where
  root := `BelaySqlCheck
  supportInterpreter := true
