# Experiments for query results as bags: the prototype bag module, the current model outputs,
# native SQLite probes and the kernel cost of two bag representations, against the pinned
# toolchain, model package and SQLite.
{ system ? builtins.currentSystem }:
let
  pkgs = import ../../build-support/locked-nixpkgs.nix { inherit system; };
  build = import ../../build-support/default.nix { inherit system pkgs; };
  native = import ../../nix/sqlite.nix { inherit pkgs; };
  source = pkgs.lib.fileset.toSource {
    root = ./.;
    fileset = pkgs.lib.fileset.fileFilter
      (file: file.hasExt "lean" || file.hasExt "py" || file.hasExt "sql" || file.hasExt "sh"
        || file.hasExt "expected") ./.;
  };
in pkgs.runCommand "bag-results-experiments" {
  nativeBuildInputs = [ build.leanToolchain pkgs.python3 pkgs.coreutils pkgs.diffutils pkgs.scc ];
} ''
  cp -r ${source} work
  chmod -R u+w work
  cd work
  export LEAN_PATH="$PWD:${build.modelPackage}/.lake/build/lib/lean"
  mkdir -p "$out"
  python3 check.py "$out" ${native.sqlite}/bin/sqlite3
  timeout 60 scc --no-gitignore --no-ignore --no-scc-ignore --format json \
    $(find . -name '*.lean' -not -path './kernel-cost/*' | sort) > "$out/lines.json"
  printf '%s\n' '${build.modelPackage}' > "$out/model-path.txt"
  printf '%s\n' '${build.leanToolchain}' > "$out/toolchain-path.txt"
  printf '%s\n' '${native.sqlite}' > "$out/sqlite-path.txt"
''
