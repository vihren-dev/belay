# Invoke with nix-build build-support/default.nix -A TARGET (flakes enabled).
{ root ? ../.
, system ? builtins.currentSystem
, pkgs ? import ./locked-nixpkgs.nix { inherit system; }
, native ? import ../nix/sqlite.nix { inherit pkgs; }
, referenceRevision ? null
}:
let
  sources = import ./sources.nix { inherit (pkgs) lib; inherit root; };
  leanToolchain = import ./lean-toolchain.nix { inherit pkgs; };
  inventoryTools = pkgs.lib.fileset.toSource {
    root = ../.;
    fileset = pkgs.lib.fileset.unions [ ../tools/public_doc_coverage.py ../tools/public_doc_inventory.py ];
  };
  # One Nix derivation for each Lean package under packages/ (ADR 0010 section 7).
  leanPackage = arguments: import ./lean-package.nix ({ inherit pkgs leanToolchain; } // arguments);
in rec {
  inherit leanToolchain sources;
  # The standalone model and its separate transport codec, without application inputs.
  modelPackage = leanPackage {
    pname = "belay-sqlite-model";
    directory = "packages/belay-sqlite-model";
    source = sources.model;
    # Downstream precompiled modules replay these objects and shared libraries.
    targets = [ "Belay.Sqlite.Model" "Belay.Sqlite.Model.Codec"
                "Belay.Sqlite.Model:shared" "Belay.Sqlite.Model.Codec:shared" ];
  };
  sqlite3534 = native.sqlite3534;
  docGen4 = import ./doc-gen4.nix { inherit pkgs leanToolchain; };
  apiReferenceCore = import ./api-reference-core.nix { inherit pkgs leanToolchain docGen4; };
  apiReferenceBase = import ./api-reference.nix {
    inherit pkgs leanToolchain docGen4 modelPackage;
    core = apiReferenceCore;
  };
  apiReference = import ./api-reference-links.nix {
    inherit pkgs;
    base = apiReferenceBase;
    revision = referenceRevision;
  };
  publicDocumentation = import ./public-documentation.nix {
    inherit pkgs leanToolchain inventoryTools docTools modelPackage;
  };
  conformanceNative = import ./conformance-native.nix { inherit pkgs; };
  conformanceDocs = import ./conformance-docs.nix {
    inherit pkgs; inherit (conformanceNative) fixture upstream;
  };
  allTests = import ./tests.nix {
    inherit pkgs leanToolchain native conformance modelPackage root;
    parserLibrary = parserLibrary.testRoot;
    inherit leanPackages surfacePackage textPackage;
  };
  # Suites that only main pushes and scheduled runs build (`just test-scheduled`), so that the CI
  # time of pull requests does not grow; tests/nix_scheduled_suites.json lists them.
  scheduledSuites = builtins.fromJSON (builtins.readFile ../tests/nix_scheduled_suites.json);
  tests = pkgs.lib.removeAttrs allTests scheduledSuites;
  scheduledTests = pkgs.lib.getAttrs scheduledSuites allTests;
  # The scheduled suites of the mutants of the model, which CI runs in their own job, one runner
  # each (`just test-mutants SUITE`); tests/nix_mutant_suites.json lists them.
  mutantSuites = builtins.fromJSON (builtins.readFile ../tests/nix_mutant_suites.json);
  # `just test` skips the slow model comparisons, the kernel proofs of the coverage cases, the frozen evidence and the locked-corpus
  # validation; `just test-full` runs them.
  developmentTests = pkgs.lib.removeAttrs tests [ "model" "coverageStatements" "coverageFeatures" "frozen" "corpora" ];
  # One folder per suite, named after the suite, for the justfile recipes: for example
  # build/nix-tests-full/frozen/junit.xml. `nix-build -A tests` would instead number its
  # out-links in alphabetical order of the suites.
  testReports = pkgs.linkFarm "sqlite-verifier-test-reports" tests;
  developmentTestReports = pkgs.linkFarm "sqlite-verifier-development-test-reports" developmentTests;
  scheduledTestReports = pkgs.linkFarm "sqlite-verifier-scheduled-test-reports" scheduledTests;
  # The scheduled suites that the `full` scope runs in the check job: all but the mutant suites.
  scheduledCheckReports = pkgs.linkFarm "sqlite-verifier-scheduled-check-reports"
    (pkgs.lib.removeAttrs scheduledTests mutantSuites);
  # The binding of the parser library and the translation of SQL text, below the surface
  # (ADR 0016, D2, amended).
  textPackage = leanPackage {
    pname = "belay-sqlite-text";
    directory = "packages/belay-sqlite-text";
    source = sources.text;
    # The shared libraries are what Lake loads for a file that imports the translation.
    # The program translates the conformance harness's SQL texts.
    targets = [ "BelaySqliteText" "BelaySqliteText:shared" "parserShim:shared" "belay-sqlite-translate" ];
    requires."packages/belay-sqlite-model" = modelPackage;
    # The translation's precompiled modules call the model's compiled code.
    sharedRequires = [ "packages/belay-sqlite-model" ];
    executables = true;
    environment.BELAY_PARSER_LIBRARY = parserLibrary.library;
  };
  # Sampling belongs to the surface; the model and conformance runner do not require it.
  plausiblePackage = import ./plausible.nix { inherit pkgs leanToolchain; };
  # The surface that users import (ADR 0016, D1). It is not part of the conformance runtime;
  # tests.surface checks it and its layer rules.
  surfacePackage = let
    # Read-only evaluation can compute a filtered store path before that path exists.
    manifest = builtins.fromJSON (builtins.readFile (root + /packages/belay/lake-manifest.json));
    sampler = pkgs.lib.findFirst (entry: entry.name == "plausible") null manifest.packages;
    url = "https://github.com/leanprover-community/plausible";
    localManifest = manifest // { packages = map (entry:
      if entry.name != "plausible" then entry else {
        inherit (entry) name scope inherited manifestFile configFile;
        type = "path"; dir = ".lake/packages/plausible";
      }) manifest.packages; };
  in assert sampler.type == "git" && sampler.url == url && sampler.rev == plausiblePackage.revision;
  (leanPackage {
    pname = "belay";
    directory = "packages/belay";
    source = sources.surface;
    # The shared library is what Lake loads for a file that imports `Belay`, after the text package's.
    # The SQL-file checker is the only executable (ADR 0017, S7); it is not part of the conformance runtime.
    targets = [ "Belay" "Belay:shared" "belay-sql-check" ];
    executables = true;
    requires."packages/belay-sqlite-model" = modelPackage;
    requires."packages/belay-sqlite-text" = textPackage;
    requires."packages/belay/.lake/packages/plausible" = plausiblePackage;
    sharedRequires = [ "packages/belay-sqlite-model" "packages/belay-sqlite-text"
      "packages/belay/.lake/packages/plausible" ];
    environment.BELAY_PARSER_LIBRARY = parserLibrary.library;
  }).overrideAttrs (_: {
    # Nix supplies this exact source; Lake must use the local output without cloning it.
    postPatch = ''
      substituteInPlace lakefile.lean --replace-fail \
        'require plausible from git "${url}" @ "${plausiblePackage.revision}"' \
        'require plausible from ".lake/packages/plausible"'
      cp ${pkgs.writeText "surface-lake-manifest.json" (builtins.toJSON localManifest)} lake-manifest.json
    '';
  });
  # The in-process SQLite parser library of the harness and the surface; tests.parserLibrary checks it.
  parserLibrary = import ./parser-library.nix { inherit pkgs root; };
  verifierConformance = leanPackage {
    pname = "sqlite-verifier-conformance-package";
    directory = "packages/verifier-conformance";
    source = sources.verifierConformance;
    targets = [ "VerifierConformance" "conformance-runner" ];
    requires."packages/belay-sqlite-model" = modelPackage;
    executables = true;
  };
  # The built Lean packages by their folder in the repository layout; tests.packages replays them.
  leanPackages = {
    "packages/belay-sqlite-model" = modelPackage; "packages/verifier-conformance" = verifierConformance;
    "packages/public-doc-tools" = docTools;
  };
  # The documentation inventory's Lean part; publicDocumentation and tests.documentation use it.
  docTools = leanPackage {
    pname = "sqlite-verifier-doc-tools";
    directory = "packages/public-doc-tools";
    source = sources.docTools;
    targets = [ "PublicDocSyntax" "PublicDocInventory" ];
  };
  # The conformance runner and its library modules, and the translation program, which the harness
  # and the judge's subject run. The program finds the parser library by its path in the Nix store.
  conformanceRuntime = pkgs.runCommand "sqlite-verifier-conformance-runtime" { } ''
    mkdir -p "$out/.lake/build/bin" "$out/.lake/build/lib"
    cp -R ${verifierConformance}/.lake/build/lib/lean "$out/.lake/build/lib/"
    cp ${verifierConformance}/.lake/build/bin/conformance-runner "$out/.lake/build/bin/"
    cp ${textPackage}/.lake/build/bin/belay-sqlite-translate "$out/.lake/build/bin/"
  '';
  conformance = pkgs.runCommand "sqlite-verifier-conformance" {} ''
    mkdir -p "$out"
    ln -s ${leanToolchain} "$out/lean"
    ln -s ${conformanceRuntime}/.lake "$out/.lake"
    mkdir -p "$out/packages"
    ln -s ${modelPackage} "$out/packages/belay-sqlite-model"
  '';
  # The runner built against an instrumented copy of the model's sources, which compiles here.
  conformanceCoverage = (leanPackage {
    pname = "sqlite-verifier-conformance-coverage";
    directory = "packages/verifier-conformance";
    source = sources.verifierConformance;
    targets = [ "conformance-runner" ];
    requires."packages/belay-sqlite-model" = sources.model;
    executables = true;
  }).overrideAttrs (old: {
    postPatch = ''
      ${pkgs.python3}/bin/python3 ${../conformance/instrument_model.py} ../..
    '';
    installPhase = ''
      mkdir -p "$out/.lake/build/bin"
      cp .lake/build/bin/conformance-runner "$out/.lake/build/bin/"
      cp ../../coverage-sites.json "$out/"
    '';
  });
}
