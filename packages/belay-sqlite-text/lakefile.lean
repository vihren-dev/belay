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

/-- A parser or a tokenizer of the parser library, as {lit}`parser/generated/manifest.json` lists it. -/
structure ParserPart where
  /-- The folder of its generated C below {lit}`parser/generated/parsers` or
  {lit}`parser/generated/tokenizers`. -/
  folder : String
  /-- The prefix of its symbols, for example {lit}`Syntax_315770c3787c6a51`. -/
  «prefix» : String
  deriving FromJson

/-- One grammar of the parser library: a parser and a tokenizer, by their folders. -/
structure ParserGrammar where
  /-- The prefix of the grammar's parse function, for example {lit}`Grammar_513216cb503b3e79`. -/
  «prefix» : String
  parser : String
  tokenizer : String
  deriving FromJson

/-- The manifest of the generated C: the compile flags of every unit, the parsers, the
tokenizers and the grammars. -/
structure ParserManifest where
  flags : Array String
  parsers : Array ParserPart
  tokenizers : Array ParserPart
  grammars : Array ParserGrammar
  deriving FromJson

/-- The symbol prefix of the part of {lit}`parts` in {lit}`folder`. -/
def ParserManifest.prefixOf (parts : Array ParserPart) (folder : String) : Except String String :=
  match parts.find? (·.folder == folder) with
  | some part => .ok part.prefix
  | none => .error (s!"parser/generated/manifest.json names no parser or tokenizer folder {folder}; " ++
      "restore parser/generated from version control, or run `just parser-sources` on Linux")

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

/-- The static library of the parser: the C units of the parser library, one for each parser,
one for each tokenizer and one for each grammar, and the shim that gives the library's C API
Lean's calling convention. Lake also makes its shared library, which the precompiled modules
load. -/
extern_lib parserLibrary pkg := do
  let parser ← IO.FS.realPath (parserFolder pkg)
  let manifestPath := parser / "generated" / "manifest.json"
  let manifest : ParserManifest ← IO.ofExcept <| fromJson? (← IO.ofExcept <| Json.parse (← IO.FS.readFile manifestPath))
  let file (path : FilePath) : FetchM (Job (Array FilePath)) := return (← inputTextFile path).map (#[·])
  let folder (path : FilePath) : FetchM (Job (Array FilePath)) := inputDir path true (fun _ => true)
  let mut jobs := #[← file manifestPath, ← folder (parser / "generated"), ← folder (parser / "c-headers")]
  for name in ["library.h", "runtime.h", "tokenizer.c", "library_prefix.h"] do
    jobs := jobs.push (← file (parser / name))
  let inputs := (Job.collectArray jobs).map (·.flatten)
  let parsers := FilePath.mk "generated" / "parsers"
  let tokenizers := FilePath.mk "generated" / "tokenizers"
  let mut objects := #[]
  for part in manifest.parsers do
    objects := objects.push (← compileParserUnit pkg manifest inputs "library_parser.c"
      ("parser-" ++ part.folder ++ ".o") #[parsers / part.folder, "."] #[])
  for part in manifest.tokenizers do
    objects := objects.push (← compileParserUnit pkg manifest inputs "library_tokenizer.c"
      ("tokenizer-" ++ part.folder ++ ".o") #[tokenizers / part.folder, "."] #["-DTOKENIZER_PREFIX=" ++ part.prefix])
  for grammar in manifest.grammars do
    let parserPrefix ← IO.ofExcept <| ParserManifest.prefixOf manifest.parsers grammar.parser
    let tokenizerPrefix ← IO.ofExcept <| ParserManifest.prefixOf manifest.tokenizers grammar.tokenizer
    objects := objects.push (← compileParserUnit pkg manifest inputs "library_grammar.c"
      ("grammar-" ++ grammar.prefix ++ ".o") #[parsers / grammar.parser, tokenizers / grammar.tokenizer, "."]
      #["-DGRAMMAR_PREFIX=" ++ grammar.prefix, "-DPARSER_PREFIX=" ++ parserPrefix,
        "-DTOKENIZER_PREFIX=" ++ tokenizerPrefix])
  objects := objects.push (← compileParserUnit pkg manifest inputs "library.c" "library.o"
    #[FilePath.mk "generated", FilePath.mk "."] #[])
  let shim ← inputTextFile (pkg.dir / "c" / "parser_shim.c")
  objects := objects.push (← buildLeanO (pkg.buildDir / "c" / "parser_shim.o") shim #["-I", parser.toString] #["-fPIC"])
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "belayParserLibrary") objects

/-- The translation program of the conformance harness ({lit}`TranslationProgram.lean`). It
contains the parser library: Lake links the package's static library. -/
lean_exe «belay-sqlite-translate» where
  root := `TranslationProgram
