import Lake
open Lake DSL System

/-! The surface: the library that users import, {lit}`Belay`, with SQLite under
{lit}`Belay.Sqlite` (ADR 0016, D1). It calls the SQLite parser library as native code while a
file elaborates, so its modules are precompiled and linked with the library. -/

/-- The installed parser library: the folder with {lit}`lib` and {lit}`include` that
{lit}`nix-build build-support/default.nix -A parserLibrary.library` makes, from the
environment variable {lit}`BELAY_PARSER_LIBRARY`. Lake reads it when it loads this file; after
a change, run Lake with {lit}`-R`. -/
def parserLibrary : FilePath := run_io do
  match ← IO.getEnv "BELAY_PARSER_LIBRARY" with
  | some path => return path
  | none => throw <| IO.userError ("BELAY_PARSER_LIBRARY is not set; build the parser library with " ++
      "`nix-build build-support/default.nix -A parserLibrary.library` and set it to the result")

package belay

require belaySqliteModel from "../belay-sqlite-model"

/-- The surface library. Its modules are precompiled, so that the interpreter that runs a
file's commands calls the parser library's native code. The library names its modules: a root
{lit}`Belay` would make Lake take every module under {lit}`Belay`, the model's too, as part of
this package. -/
@[default_target]
lean_lib Belay where
  roots := #[]
  globs := #[.one `Belay, .one `Belay.Sqlite, .one `Belay.Sqlite.Grammar, .one `Belay.Sqlite.Parse,
    .one `Belay.Sqlite.ParseCommand, .one `Belay.Sqlite.ParserLibrary, .one `Belay.Sqlite.ParseTree,
    .andSubmodules `Belay.Sqlite.Translation]
  precompileModules := true
  moreLinkArgs := #["-L" ++ (parserLibrary / "lib").toString, "-lsqlite-verifier-parser",
    "-Wl,-rpath," ++ (parserLibrary / "lib").toString]

/-- The C functions that give the parser library's C API Lean's calling convention. -/
target parserShim.o pkg : FilePath := do
  let object := pkg.buildDir / "c" / "parser_shim.o"
  let source ← inputTextFile <| pkg.dir / "c" / "parser_shim.c"
  buildLeanO object source #["-I", (parserLibrary / "include").toString, "-fPIC"]

/-- The library of {lit}`parserShim.o`, which the precompiled modules link. -/
extern_lib parserShim pkg := do
  let object ← fetch <| pkg.target ``parserShim.o
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "belayParserShim") #[object]
