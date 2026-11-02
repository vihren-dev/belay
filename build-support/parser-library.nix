# The SQLite parser library (see docs/sqlite-parser.md, "Library build and dialect table").
# Nix reads parser/dialects.json and makes one derivation for each release, one for each
# distinct grammar identity and one that links the library, so a new release or grammar
# builds only its own derivations. The `parserLibrary` suite of tests.nix checks the result.
# The C that the last stage compiles is committed under parser/generated (ADR 0023): the Lake
# build of the text package compiles the same files with the same headers and flags.
{ pkgs, leanToolchain, root ? ../. }:
let
  inherit (pkgs) lib;
  fs = lib.fileset;
  inherit (pkgs.stdenv.hostPlatform) isLinux;
  table = builtins.fromJSON (builtins.readFile (root + /parser/dialects.json));
  libraryName = "libsqlite-verifier-parser" + (if isLinux then ".so" else ".dylib");
  # The identity digits in a grammar's symbol prefix and derivation names;
  # parser/library_steps.py fails if two grammars share them.
  prefixDigits = 16;
  short = identity: builtins.substring 0 prefixDigits identity;
  prefix = identity: "Syntax_" + short identity;
  # The build steps and the grammar transform; the release and grammar files come per derivation.
  steps = map (name: root + "/parser/${name}.py")
    [ "library_steps" "grammar_sources" "dialect_table" "library_metadata" "generate" ];
  source = files: fs.toSource { inherit root; fileset = fs.unions files; };
  releaseOf = version: lib.findFirst (release: release.version == version)
    (throw "parser/dialects.json has a dialect of release ${version}, which its release list does not name")
    table.releases;
  # Only this release and its dialects, so a new release leaves the other derivations unchanged.
  releaseTable = release: builtins.toFile "dialects-${release.version}.json" (builtins.toJSON {
    releases = [ release ];
    dialects = builtins.filter (dialect: dialect.version == release.version) table.dialects;
  });
  # Lemon's outputs for the release, after the hash and dialect identity checks.
  releaseBuild = release: let directory = "parser/${release.sources}"; in pkgs.stdenv.mkDerivation {
    pname = "sqlite-verifier-parser-release";
    inherit (release) version;
    src = source (steps ++ [ (root + "/${directory}") ]);
    nativeBuildInputs = [ pkgs.python3 ];
    dontConfigure = true;
    dontInstall = true;
    buildPhase = ''
      python3 -m parser.library_steps hashes ${directory}
      mkdir -p "$out"
      $CC ${directory}/lemon.c -o "$out/lemon"
      "$out/lemon" -q -d"$out" -T${directory}/lempar.c ${directory}/parse.y
      rm "$out/parse.c"
      "$out/lemon" -E ${directory}/parse.y > "$out/preprocessed.y"
      "$out/lemon" -g ${directory}/parse.y > "$out/grammar.y"
      python3 -m parser.library_steps release --directory ${directory} --table ${releaseTable release} \
        --preprocessed "$out/preprocessed.y" --output "$out/release.json"
    '';
  };
  releases = lib.listToAttrs (map (release: lib.nameValuePair release.version (releaseBuild release)) table.releases);
  # Each distinct identity, built from the first dialect's release; equal identities have equal sources.
  identities = lib.unique (map (dialect: dialect.grammar) table.dialects);
  releaseOfGrammar = identity:
    releaseOf (lib.findFirst (dialect: dialect.grammar == identity) null table.dialects).version;
  # The generated parser of one grammar, with its own symbol prefix and its production check.
  grammarSources = identity: let
    release = releaseOfGrammar identity;
    directory = "parser/${release.sources}";
    built = releases.${release.version};
  in pkgs.stdenv.mkDerivation {
    pname = "sqlite-verifier-parser-grammar";
    version = short identity;
    src = source (steps ++ map (name: root + "/${directory}/${name}") [ "lempar.c" "sqlite3.c" ]);
    nativeBuildInputs = [ pkgs.python3 ];
    dontConfigure = true;
    dontInstall = true;
    buildPhase = ''
      mkdir -p "$out"
      cp ${built}/preprocessed.y ${built}/grammar.y ${built}/parse.h "$out/"
      python3 parser/generate.py ${directory} "$out" --name ${prefix identity}
      ${built}/lemon -q -T${directory}/lempar.c "$out/syntax.y"
      python3 -m parser.library_steps grammar --directory "$out" --identity ${identity} --prefix ${prefix identity}
    '';
  };
  grammars = lib.genAttrs identities grammarSources;
  # The compile flags that every build of the committed C shares (ADR 0023, D2 and D3). The Lake
  # build of the text package reads them from the manifest; the C library headers of
  # parser/c-headers declare what these two SQLite options leave in the code.
  compileFlags = [ "-O1" "-std=c99" "-fPIC" "-fvisibility=hidden" "-DSQLITE_OS_OTHER=1" "-DSQLITE_THREADSAFE=0" ];
  manifest = {
    flags = compileFlags;
    grammars = map (identity: {
      prefix = prefix identity;
      folder = short identity;
      sources = (releaseOfGrammar identity).sources;
    }) identities;
  };
  # The tree that is committed as parser/generated (ADR 0023, D1): the C files that the compile
  # needs and that a generator writes, one folder for each grammar, and the manifest. `just
  # parser-sources` writes this tree into the checkout, and the `parserSources` suite compares it.
  generated = pkgs.runCommand "sqlite-verifier-parser-generated" {
    src = source steps;
    nativeBuildInputs = [ pkgs.python3 ];
  } ''
    cd "$src"
    mkdir -p "$out"
    python3 -m parser.library_steps sources --table ${builtins.toFile "dialects.json" (builtins.toJSON table)} \
      ${lib.concatMapStringsSep " " (release: "--release ${releases.${release.version}}/release.json") table.releases} \
      ${lib.concatMapStringsSep " " (identity: "--grammar ${grammars.${identity}}/grammar.json") identities} \
      --output "$out"
    ${lib.concatMapStringsSep "\n" (identity: ''
      mkdir -p "$out/${short identity}"
      for name in syntax.c syntax.h parse.h token_map.inc token_names.inc; do
        # Lemon wrote the store path of the grammar derivation into its #line directives and
        # comments; the committed copy must not depend on that path.
        sed 's|${grammars.${identity}}/||g' ${grammars.${identity}}/$name > "$out/${short identity}/$name"
      done
    '') identities}
    python3 -c 'import json, sys; print(json.dumps(json.load(open(sys.argv[1])), indent=2))' \
      ${builtins.toFile "manifest.json" (builtins.toJSON manifest)} > "$out/manifest.json"
  '';
  # The objects of one grammar from the committed files: its tokenizer, with SQLite's symbols
  # internal, and its parser. `compiler` and `flags` come from the caller: the library uses Lean's
  # clang, as Lake does, and the sanitized build uses the C compiler of Nix.
  grammarObjects = { compiler, flags }: identity: let
    release = releaseOfGrammar identity;
    directory = "parser/${release.sources}";
  in pkgs.runCommandCC "sqlite-verifier-parser-objects-${short identity}" {
    src = source (map (name: root + "/parser/${name}")
      [ "runtime.h" "tokenizer.c" "library_prefix.h" "library_tokenizer.c" "library_grammar.c" "c-headers"
        "generated/${short identity}" ]
      ++ map (name: root + "/${directory}/${name}") [ "sqlite3.c" "sqlite3.h" ]);
  } ''
    mkdir -p "$out"
    for unit in library_tokenizer library_grammar; do
      ${compiler} -c ${flags} -DGRAMMAR_PREFIX=${prefix identity} -I"$src/parser/generated/${short identity}" \
        -I"$src/${directory}" -I"$src/parser" -isystem "$src/parser/c-headers" "$src/parser/$unit.c" -o "$out/$unit.o"
    done
  '';
  # Link all grammars with the API; the export check runs unless sanitizer runtimes add symbols.
  # The objects are compiled from the committed files (D3); the linker is the C compiler of Nix.
  library = { name, compiler, flags, exportCheck }: let
    objects = map (grammarObjects { inherit compiler flags; }) identities;
  in pkgs.runCommandCC name {
    src = source (steps ++ map (name: root + "/parser/${name}")
      [ "library.c" "library.h" "runtime.h" "c-headers" "generated/library_grammars.inc" "generated/library_metadata.inc" ]);
    nativeBuildInputs = [ pkgs.python3 ];
  } ''
    cd "$src"
    work="$TMPDIR/library"
    mkdir -p "$work" "$out/lib"
    ${compiler} -c ${flags} -Iparser/generated -Iparser -isystem parser/c-headers parser/library.c -o "$work/library.o"
    $CC ${flags} ${if isLinux then "-shared" else "-dynamiclib"} -o "$out/lib/${libraryName}" \
      ${lib.concatMapStringsSep " " (objects: "${objects}/*.o") objects} "$work/library.o" \
      ${lib.optionalString isLinux "-lm -lpthread -ldl"}
    ${lib.optionalString exportCheck ''python3 -m parser.library_steps exports "$out/lib/${libraryName}"''}
  '';
  # Lean's clang with Lean's flags, as Lake compiles the units: `leanc` adds the sysroot, the
  # toolchain's compiler headers and Lean's include folder.
  leanCompiler = "${leanToolchain}/bin/leanc";
  # The sanitizer job's build; LeakSanitizer is part of AddressSanitizer on Linux.
  sanitizerFlags = "-O1 -g -fno-omit-frame-pointer -fsanitize=address,undefined -fno-sanitize-recover=all";
  # The sanitized build adds the sanitizer flags to the flags of the manifest, with its own compiler.
  sanitizedFlags = "${lib.concatStringsSep " " (builtins.filter (flag: flag != "-O1") compileFlags)} ${sanitizerFlags}";
  normal = library { name = "sqlite-verifier-parser-library"; compiler = leanCompiler; flags = lib.concatStringsSep " " compileFlags; exportCheck = true; };
  sanitized = library { name = "sqlite-verifier-parser-library-sanitized"; compiler = "$CC"; flags = sanitizedFlags; exportCheck = false; };
  # Every parser test input and every distinct SQL text of every retained corpus.
  inputs = pkgs.runCommand "sqlite-verifier-parser-inputs" {
    src = source ([ (root + /tests/__init__.py) (root + /tests/parser_inputs.py) (root + /tests/parser_library_inputs.py) ]
      ++ map (version: root + "/conformance/corpus-v${toString version}") [ 1 2 3 4 5 ]);
    nativeBuildInputs = [ pkgs.python3 ];
  } ''
    cd "$src"
    python3 -m tests.parser_library_inputs --output "$out" \
      ${lib.concatMapStringsSep " " (version: "--corpus conformance/corpus-v${toString version}") [ 1 2 3 4 5 ]}
  '';
  driver = root + /tests/parser_library_driver.c;
in {
  inherit releases grammars inputs generated;
  library = normal;
  # The runtime root of the parserLibrary test suite: the library, the driver, the
  # inputs and, on Linux, the sanitized build.
  testRoot = pkgs.runCommandCC "sqlite-verifier-parser-library-tests" {} ''
    mkdir -p "$out/bin" "$out/lib"
    ln -s ${normal}/lib/${libraryName} "$out/lib/${libraryName}"
    $CC -std=c99 -O1 ${driver} -o "$out/bin/parser-library-driver" ${lib.optionalString isLinux "-ldl"}
    ln -s ${inputs} "$out/inputs"
    ${lib.optionalString isLinux ''
      mkdir -p "$out/sanitized/bin" "$out/sanitized/lib"
      ln -s ${sanitized}/lib/${libraryName} "$out/sanitized/lib/${libraryName}"
      $CC -std=c99 ${sanitizerFlags} ${driver} -o "$out/sanitized/bin/parser-library-driver" -ldl
    ''}
  '';
} // lib.optionalAttrs isLinux { sanitizedLibrary = sanitized; }
