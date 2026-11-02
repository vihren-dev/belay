import Lake
open Lake DSL System
open Lean (Json FromJson fromJson?)

/-! The SQL text package below the surface (ADR 0016, D2, amended; ADR 0017, D2): the binding of
the SQLite parser library and the translation of SQL text to the model's statement syntax. The
surface and the conformance harness use the same translation. The translation calls the parser
library as native code, so its modules are precompiled and linked with the library. The package
compiles the library's C code itself (ADR 0023), so a Lake build needs only the pinned Lean: no
system C compiler, no C library headers and no Nix. The package's program translates the
harness's batches of SQL texts. -/

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

/-- One grammar of the parser library, as {lit}`parser/generated/manifest.json` lists it. -/
structure ParserGrammar where
  /-- The Lemon prefix of the grammar's symbols, for example {lit}`Syntax_7c0495821ae35f29`. -/
  «prefix» : String
  /-- The folder of the grammar's generated C below {lit}`parser/generated`. -/
  folder : String
  /-- The folder of the grammar's SQLite release below {lit}`parser`. -/
  sources : String
  deriving FromJson

/-- The manifest of the generated C: the compile flags of every unit and the grammars. -/
structure ParserManifest where
  flags : Array String
  grammars : Array ParserGrammar
  deriving FromJson

/-- The folder {lit}`parser` of the repository, relative to the package folder, so that it also
works for a package that Lake fetches from git with a sub-directory. -/
def parserFolder (pkg : Package) : FilePath := pkg.dir / ".." / ".." / "parser"

/-- Compile one C unit of the parser library with Lean's {lit}`clang` and Lean's flags
({lit}`buildLeanO`), the flags of the manifest, {lit}`defines`, and the C library declarations of
{lit}`parser/c-headers` as system headers. The folders of {lit}`includes` are below {lit}`parser`.
Locations are weak arguments: they stay out of the trace, so a different path of the repository does
not rebuild the unit. The unit depends on {lit}`inputs`, the files that it includes, which Lake
does not find itself. -/
def compileParserUnit (pkg : Package) (manifest : ParserManifest) (inputs : Job (Array FilePath))
    (source : FilePath) (object : FilePath) (includes : Array FilePath) (defines : Array String) :
    FetchM (Job FilePath) := do
  let parser ← IO.FS.realPath (parserFolder pkg)
  let sourceJob ← inputTextFile (parser / source)
  let weak := includes.foldl (fun args folder => args ++ #["-I", (parser / folder).toString]) #[] ++
    #["-isystem", (parser / "c-headers").toString]
  buildLeanO (pkg.buildDir / "c" / "parser" / object) (sourceJob.zipWith (fun source _ => source) inputs)
    weak (manifest.flags ++ defines)

/-- The static library of the parser: the C units of the parser library, for each grammar its
tokenizer and its generated parser, and the shim that gives the library's C API Lean's calling
convention. Lake also makes its shared library, which the precompiled modules load. -/
extern_lib parserLibrary pkg := do
  let parser ← IO.FS.realPath (parserFolder pkg)
  let manifestPath := parser / "generated" / "manifest.json"
  let manifest : ParserManifest ← IO.ofExcept <| fromJson? (← IO.ofExcept <| Json.parse (← IO.FS.readFile manifestPath))
  let file (path : FilePath) : FetchM (Job (Array FilePath)) := return (← inputTextFile path).map (#[·])
  let folder (path : FilePath) : FetchM (Job (Array FilePath)) := inputDir path true (fun _ => true)
  let mut jobs := #[← file manifestPath, ← folder (parser / "generated"), ← folder (parser / "c-headers")]
  for name in ["library.h", "runtime.h", "tokenizer.c", "library_prefix.h"] do
    jobs := jobs.push (← file (parser / name))
  for grammar in manifest.grammars do
    jobs := jobs ++ #[← file (parser / grammar.sources / "sqlite3.c"), ← file (parser / grammar.sources / "sqlite3.h")]
  let inputs := (Job.collectArray jobs).map (·.flatten)
  let mut objects := #[]
  for grammar in manifest.grammars do
    let includes := #[FilePath.mk "generated" / grammar.folder, FilePath.mk grammar.sources, FilePath.mk "."]
    for unit in ["library_tokenizer", "library_grammar"] do
      objects := objects.push (← compileParserUnit pkg manifest inputs (unit ++ ".c")
        (grammar.folder ++ "-" ++ unit ++ ".o") includes #["-DGRAMMAR_PREFIX=" ++ grammar.prefix])
  objects := objects.push (← compileParserUnit pkg manifest inputs "library.c" "library.o"
    #[FilePath.mk "generated", FilePath.mk "."] #[])
  let shim ← inputTextFile (pkg.dir / "c" / "parser_shim.c")
  objects := objects.push (← buildLeanO (pkg.buildDir / "c" / "parser_shim.o") shim #["-I", parser.toString] #["-fPIC"])
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "belayParserLibrary") objects

/-- The translation program of the conformance harness ({lit}`TranslationProgram.lean`). It
contains the parser library: Lake links the package's static library. -/
lean_exe «belay-sqlite-translate» where
  root := `TranslationProgram
