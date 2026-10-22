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

/-- The surface library. Its modules are precompiled, so that the interpreter that runs a
file's commands calls the parser library's native code. The library names its modules: a root
{lit}`Belay` would make Lake take every module under {lit}`Belay`, the model's and the text
package's too, as part of this package. -/
@[default_target]
lean_lib Belay where
  roots := #[]
  globs := #[.one `Belay, .one `Belay.Sqlite, .one `Belay.Sqlite.ParseCommand, .one `Belay.Sqlite.Values, .one `Belay.Sqlite.Database,
    .one `Belay.Sqlite.Script, .one `Belay.Sqlite.SqlLiteral, .one `Belay.Sqlite.SqlTerm]
  precompileModules := true
