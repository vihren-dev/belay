# Inspect the selected built libraries, including source modules outside umbrella imports.
{ pkgs, leanToolchain, dependencyTools, modelPackage, textPackage,
  surfacePackage, verifierConformance, plausiblePackage }:
let
  packages = {
    belay-sqlite-model = modelPackage;
    belay-sqlite-text = textPackage;
    belay = surfacePackage;
    verifier-conformance = verifierConformance;
  };
  libraries = builtins.attrValues packages ++ [ plausiblePackage ];
in pkgs.runCommand "sqlite-verifier-theorem-dependencies" {
  nativeBuildInputs = [ leanToolchain pkgs.python3 ];
} ''
  mkdir -p packages
  ${pkgs.lib.concatStrings (pkgs.lib.mapAttrsToList (name: package: ''
    ln -s ${package} packages/${name}
  '') packages)}
  export PYTHONPATH=${dependencyTools}
  python3 -m tools.theorem_dependencies --root "$PWD" \
    --lean ${leanToolchain}/bin/lean --output "$out" \
    --lean-path ${pkgs.lib.escapeShellArg (pkgs.lib.concatMapStringsSep ":" (package: "${package}/.lake/build/lib/lean") libraries)}
''
