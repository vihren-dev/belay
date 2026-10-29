# Explicit proof-design evidence against unchanged pinned production packages.
{ system ? builtins.currentSystem }:
let
  pkgs = import ../../build-support/locked-nixpkgs.nix { inherit system; };
  build = import ../../build-support/default.nix { inherit system pkgs; };
  libraries = pkgs.symlinkJoin {
    name = "proof-boundaries-libraries";
    paths = map (package: "${package}/.lake/build/lib/lean")
      [ build.modelPackage build.surfacePackage build.textPackage build.plausiblePackage ];
  };
  source = pkgs.lib.fileset.toSource {
    root = ./.;
    fileset = pkgs.lib.fileset.fileFilter
      (file: file.hasExt "lean" || file.hasExt "py" || file.name == "inventory.json") ./.;
  };
in pkgs.runCommand "proof-boundaries-experiments" {
  nativeBuildInputs = [ build.leanToolchain pkgs.python3 pkgs.coreutils ];
} ''
  mkdir work
  cp ${source}/* work/
  chmod -R u+w work
  cd work
  export LEAN_PATH="$PWD:${libraries}"
  mkdir -p "$out"
  python3 check.py "$out" ${build.modelPackage} ${build.surfacePackage} ${build.textPackage}
  printf '%s\n' '${build.modelPackage}' > "$out/model-path.txt"
  printf '%s\n' '${build.surfacePackage}' > "$out/surface-path.txt"
  printf '%s\n' '${build.leanToolchain}' > "$out/toolchain-path.txt"
''
