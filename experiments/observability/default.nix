# Explicit research probes with the repository's pin; no production or CI integration.
{ system ? builtins.currentSystem }:
let
  pkgs = import ../../build-support/locked-nixpkgs.nix { inherit system; };
  build = import ../../build-support/default.nix { inherit system pkgs; };
  source = pkgs.lib.fileset.toSource {
    root = ../..;
    fileset = pkgs.lib.fileset.unions [
      (pkgs.lib.fileset.fileFilter (file: file.hasExt "py" || file.hasExt "lean" || file.hasExt "toml") ./.)
      ../../tools ../../reviews ../../docs/review-checklist.md
      ../../conftest.py ../../pytest.ini ../../tests/__init__.py
      ../../tests/runtime_fixtures.py ../../tests/runtime_support.py
      ../../tests/test_review_log.py ../../tests/test_test_reports.py
      (pkgs.lib.fileset.fileFilter (file: file.hasExt "py") ../../conformance)
      (pkgs.lib.fileset.fileFilter (file: file.hasExt "py") ../../belay)
      ../../conformance/cases
      (pkgs.lib.fileset.fileFilter
        (file: file.hasExt "lean" && (pkgs.lib.hasPrefix "ProofCost" file.name || file.name == "SqlSourceRecord.lean"))
        ../../packages/belay/Belay/Sqlite)
    ];
  };
  python = pkgs.python3.withPackages (ps: [ ps.pytest ps.pytest-cov ps.coverage ]);
in {
  inherit python;
  probes = pkgs.runCommand "belay-observability-probes" {
    nativeBuildInputs = [ python build.leanToolchain pkgs.coreutils ];
  } ''
    export HOME="$TMPDIR"
    timeout 240 python3 ${source}/experiments/observability/run.py --root ${source} --output "$out"
  '';
}
