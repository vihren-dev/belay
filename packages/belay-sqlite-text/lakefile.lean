import Lake
open Lake DSL System

/-! The SQL text package below the surface (ADR 0016, D2, amended; ADR 0017, D2): the binding of
the SQLite parser library and the translation of SQL text to the model's statement syntax. The
surface and the conformance harness use the same translation. The translation calls the parser
library as native code, so its modules are precompiled and linked with the library. The
package's program translates the harness's batches of SQL texts. -/

/-- The installed parser library: the folder with {lit}`lib` and {lit}`include` that
{lit}`nix-build build-support/default.nix -A parserLibrary.library` makes, from the
environment variable {lit}`BELAY_PARSER_LIBRARY`. Lake reads it when it loads this file; after
a change, run Lake with {lit}`-R`. -/
def parserLibrary : FilePath := run_io do
  match ← IO.getEnv "BELAY_PARSER_LIBRARY" with
  | some path => return path
  | none => throw <| IO.userError ("BELAY_PARSER_LIBRARY is not set; build the parser library with " ++
      "`nix-build build-support/default.nix -A parserLibrary.library` and set it to the result")

/-- The linker arguments of the parser library, with its folder as the run-time search path, so
that a loaded module or the program finds the library in the Nix store. -/
def parserLinkArgs : Array String :=
  #["-L" ++ (parserLibrary / "lib").toString, "-lsqlite-verifier-parser",
    "-Wl,-rpath," ++ (parserLibrary / "lib").toString]

package belaySqliteText

require belaySqliteModel from "../belay-sqlite-model"

/-- The binding, the translation, and the requests and answers of the program. The modules are
precompiled, so that the interpreter that runs a surface file's commands calls the parser
library's native code. The library names its modules: a root {lit}`Belay` would make Lake take
every module under {lit}`Belay`, the model's too, as part of this package. -/
@[default_target]
lean_lib BelaySqliteText where
  roots := #[]
  globs := #[.one `Belay.Sqlite.Grammar, .one `Belay.Sqlite.Parse, .one `Belay.Sqlite.ParserLibrary,
    .one `Belay.Sqlite.ParseTree, .andSubmodules `Belay.Sqlite.Translation, .one `Belay.Sqlite.TranslationRequest]
  precompileModules := true
  moreLinkArgs := parserLinkArgs

/-- The C functions that give the parser library's C API Lean's calling convention. -/
target parserShim.o pkg : FilePath := do
  let object := pkg.buildDir / "c" / "parser_shim.o"
  let source ← inputTextFile <| pkg.dir / "c" / "parser_shim.c"
  buildLeanO object source #["-I", (parserLibrary / "include").toString, "-fPIC"]

/-- The library of {lit}`parserShim.o`, which the precompiled modules link. -/
extern_lib parserShim pkg := do
  let object ← fetch <| pkg.target ``parserShim.o
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "belayParserShim") #[object]

/-- The translation program of the conformance harness ({lit}`TranslationProgram.lean`). It links
the parser library with its folder in the Nix store as the run-time search path. -/
lean_exe «belay-sqlite-translate» where
  root := `TranslationProgram
  moreLinkArgs := parserLinkArgs
