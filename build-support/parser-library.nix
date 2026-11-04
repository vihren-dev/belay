# The SQLite parser library (see docs/sqlite-parser.md, "Library build and dialect table").
# The generation reads parser/dialects.json, fetches each release's two archives by their
# hashes and makes one derivation for each release, which cuts its tokenizer and generates its
# parser (parser/release_step.py), and one that writes the tree committed as parser/generated
# (ADR 0029). `just parser-sources` runs it once; no check run fetches an archive. The library
# compiles the committed files: the Lake build of the text package compiles the same files with
# the same headers and flags (ADR 0023). The `parserLibrary` suite of tests.nix checks it.
{ pkgs, leanToolchain, root ? ../. }:
let
  inherit (pkgs) lib;
  fs = lib.fileset;
  inherit (pkgs.stdenv.hostPlatform) isLinux;
  table = builtins.fromJSON (builtins.readFile (root + /parser/dialects.json));
  tableFile = builtins.toFile "dialects.json" (builtins.toJSON table);
  libraryName = "libsqlite-verifier-parser" + (if isLinux then ".so" else ".dylib");
  source = files: fs.toSource { inherit root; fileset = fs.unions files; };
  # The generation's programs, and the C files that the slice check compiles.
  steps = map (name: root + "/parser/${name}")
    [ "library_steps.py" "release_step.py" "grammar_sources.py" "dialect_table.py" "library_metadata.py"
      "generate.py" "tokenizer_cut.py" "slice_check.py" "library_tokenizer.c" "tokenizer.c" "library_prefix.h" ];
  # The release number in the archive names: 3.51.0 is 3510000.
  number = version: let parts = map lib.toInt (lib.splitString "." version); in
    toString (builtins.elemAt parts 0 * 1000000 + builtins.elemAt parts 1 * 10000 + builtins.elemAt parts 2 * 100);
  # The compile flags that every build of the committed C shares (ADR 0023, D2 and D3). The
  # generation writes them into the manifest, which the Lake build reads; the C library headers
  # of parser/c-headers declare what these two SQLite options leave in the code.
  compileFlags = [ "-O1" "-std=c99" "-fPIC" "-fvisibility=hidden" "-DSQLITE_OS_OTHER=1" "-DSQLITE_THREADSAFE=0" ];
  flagArguments = lib.concatMapStringsSep " " (flag: "--flag=${flag}") compileFlags;
  # One release: its archives, Lemon's outputs, then the release step of parser/release_step.py.
  releaseBuild = release: let
    n = number release.version;
    sourceArchive = pkgs.fetchurl {
      url = "https://sqlite.org/${release.year}/sqlite-src-${n}.zip";
      sha256 = release.sourceArchive;
    };
    amalgamationArchive = pkgs.fetchurl {
      url = "https://sqlite.org/${release.year}/sqlite-autoconf-${n}.tar.gz";
      sha256 = release.amalgamationArchive;
    };
  in pkgs.stdenv.mkDerivation {
    pname = "sqlite-verifier-parser-release";
    inherit (release) version;
    src = source steps;
    nativeBuildInputs = [ pkgs.python3 pkgs.unzip ];
    dontConfigure = true;
    dontInstall = true;
    buildPhase = ''
      sources="$TMPDIR/sources"
      mkdir -p "$sources" "$out"
      unzip -q -j ${sourceArchive} sqlite-src-${n}/src/parse.y sqlite-src-${n}/tool/lemon.c sqlite-src-${n}/tool/lempar.c -d "$sources"
      tar -xzf ${amalgamationArchive} -C "$sources" --strip-components=1 sqlite-autoconf-${n}/sqlite3.c sqlite-autoconf-${n}/sqlite3.h
      $CC "$sources/lemon.c" -o "$sources/lemon"
      (cd "$sources" && ./lemon -q -Tlempar.c parse.y && rm parse.c)
      (cd "$sources" && ./lemon -E parse.y > preprocessed.y && ./lemon -g parse.y > grammar.y)
      python3 -m parser.release_step --sources "$sources" --table ${tableFile} --version ${release.version} \
        --compiler "$CC" ${flagArguments} --parser parser --output "$out"
    '';
  };
  releases = lib.listToAttrs (map (release: lib.nameValuePair release.version (releaseBuild release)) table.releases);
  # The tree that is committed as parser/generated: `just parser-sources` writes it into the checkout.
  generated = pkgs.runCommand "sqlite-verifier-parser-generated" {
    src = source steps;
    nativeBuildInputs = [ pkgs.python3 ];
  } ''
    cd "$src"
    mkdir -p "$out"
    python3 -m parser.library_steps sources --table ${tableFile} \
      ${lib.concatMapStringsSep " " (release: "--release ${releases.${release.version}}") table.releases} \
      ${flagArguments} --output "$out"
  '';
  # The units of the committed C (ADR 0029, D3): one for each parser, one for each tokenizer and
  # one for each grammar, the pair of a parser and a tokenizer.
  manifest = builtins.fromJSON (builtins.readFile (root + /parser/generated/manifest.json));
  prefixOf = kind: folder: (lib.findFirst (entry: entry.folder == folder)
    (throw "parser/generated/manifest.json names no ${kind} ${folder}") manifest.${kind}).prefix;
  units = map (parser: {
      object = "parser-${parser.folder}"; source = "library_parser.c";
      arguments = "-Iparser/generated/parsers/${parser.folder}";
    }) manifest.parsers
    ++ map (tokenizer: {
      object = "tokenizer-${tokenizer.folder}"; source = "library_tokenizer.c";
      arguments = "-DTOKENIZER_PREFIX=${tokenizer.prefix} -Iparser/generated/tokenizers/${tokenizer.folder}";
    }) manifest.tokenizers
    ++ map (grammar: {
      object = "grammar-${grammar.prefix}"; source = "library_grammar.c";
      arguments = "-DGRAMMAR_PREFIX=${grammar.prefix} -DPARSER_PREFIX=${prefixOf "parsers" grammar.parser} "
        + "-DTOKENIZER_PREFIX=${prefixOf "tokenizers" grammar.tokenizer} "
        + "-Iparser/generated/parsers/${grammar.parser} -Iparser/generated/tokenizers/${grammar.tokenizer}";
    }) manifest.grammars
    ++ [ { object = "library"; source = "library.c"; arguments = "-Iparser/generated"; } ];
  # Link all units with the API; the export check runs unless sanitizer runtimes add symbols.
  # `compiler` and `flags` come from the caller: the library uses Lean's clang, as Lake does,
  # and the sanitized build uses the C compiler of Nix; the linker is the C compiler of Nix.
  library = { name, compiler, flags, exportCheck }: pkgs.runCommandCC name {
    src = source (map (name: root + "/parser/${name}")
      [ "library_steps.py" "release_step.py" "grammar_sources.py" "dialect_table.py" "library_metadata.py"
        "generate.py" "tokenizer_cut.py" "slice_check.py"
        "library.c" "library.h" "runtime.h" "tokenizer.c" "library_prefix.h" "library_tokenizer.c"
        "library_parser.c" "library_grammar.c" "c-headers" "generated" ]);
    nativeBuildInputs = [ pkgs.python3 ];
  } ''
    cd "$src"
    work="$TMPDIR/library"
    mkdir -p "$work" "$out/lib"
    ${lib.concatMapStringsSep "\n" (unit: ''
      ${compiler} -c ${flags} ${unit.arguments} -Iparser -isystem parser/c-headers parser/${unit.source} -o "$work/${unit.object}.o"
    '') units}
    $CC ${flags} ${if isLinux then "-shared" else "-dynamiclib"} -o "$out/lib/${libraryName}" "$work"/*.o \
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
  inherit releases inputs generated;
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
