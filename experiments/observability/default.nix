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
    ];
  };
  python = pkgs.python3.withPackages (ps: [ ps.pytest ps.pytest-cov ps.coverage ]);
in {
  inherit python;
  probes = pkgs.runCommand "belay-observability-probes" {
    nativeBuildInputs = [ python build.leanToolchain pkgs.coreutils ];
  } ''
    export HOME="$TMPDIR"
    timeout 180 python3 ${source}/experiments/observability/run.py --root ${source} --output "$out"
  '';
}
