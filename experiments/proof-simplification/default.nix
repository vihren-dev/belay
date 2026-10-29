# Compile the proof-design experiments against this checkout's pinned model.
# This is an explicit experiment target, not a new CI suite or runtime dependency.
{ system ? builtins.currentSystem }:
let
  pkgs = import ../../build-support/locked-nixpkgs.nix { inherit system; };
  build = import ../../build-support/default.nix { inherit system pkgs; };
  source = pkgs.lib.fileset.toSource {
    root = ./.;
    fileset = pkgs.lib.fileset.fileFilter
      (file: file.hasExt "lean" || builtins.elem file.name [ "check.py" "inventory.json" ]) ./.;
  };
in pkgs.runCommand "proof-simplification-experiments" {
  nativeBuildInputs = [ build.leanToolchain pkgs.python3 pkgs.coreutils ];
} ''
  mkdir work
  cp ${source}/* work/
  cd work
  export LEAN_PATH="$PWD:${build.modelPackage}/.lake/build/lib/lean"
  mkdir -p "$out"
  python3 check.py "$out" ${build.modelPackage}
  printf '%s\n' '${build.modelPackage}' > "$out/model-path.txt"
  printf '%s\n' '${build.leanToolchain}' > "$out/toolchain-path.txt"
''
