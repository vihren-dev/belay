# Experiment only: build a Lake cache seed in the Nix sandbox and use it in another derivation
# (ADR 0010 section 8).
#
# Build with (after data_path.py has written WORK_DIR/<case>/):
#   nix-build experiments/lake-cache/seed.nix -A check --arg work ./build/lake-exp/dp \
#     --argstr installation "$(readlink -f build/lake-installation)" --extra-experimental-features 'nix-command flakes'
#
# `seed` builds each case's proofs project and verify-bundle workspace with one cache
# and stages the outputs into its own output; `check` unstages the seed into a writable
# cache in another derivation and builds fresh copies of the same workspaces, failing
# if Lake compiles any workspace module. Both run in the sandbox without network.
{ pkgs ? import ../../build-support/locked-nixpkgs.nix { system = builtins.currentSystem; }
, work
, installation
, cases ? [ "small" "refutation" "atuin" ]
}:
let
  # A store path string, e.g. --argstr installation "$(readlink -f build/lake-installation)".
  installationPath = builtins.storePath installation;
  # Case sources without Lake outputs; the lakefiles name the installation's store path.
  caseSource = case: builtins.path {
    name = "lake-seed-case-${case}";
    path = work + "/${case}";
    filter = path: type: !(pkgs.lib.hasInfix "/.lake" path) && !(pkgs.lib.hasSuffix ".bundle" path);
  };
  copyCases = pkgs.lib.concatMapStrings (case: ''
    cp -R ${caseSource case} "$TMPDIR/cases/${case}"
  '') cases;
  common = ''
    export HOME="$TMPDIR" PATH="${installationPath}/lean/bin:$PATH"
    mkdir -p "$TMPDIR/cases"
    ${copyCases}
    chmod -R u+w "$TMPDIR/cases"
  '';
  workspaces = "proofs verify-bundle";
in rec {
  seed = pkgs.runCommand "lake-seed" { } ''
    ${common}
    export LAKE_CACHE_DIR="$TMPDIR/cache"
    for case in ${pkgs.lib.concatStringsSep " " cases}; do
      for workspace in ${workspaces}; do
        directory="$TMPDIR/cases/$case/$workspace"
        (cd "$directory" && lake build -o mappings.jsonl > build.log 2>&1) || { cat "$directory/build.log"; exit 1; }
        (cd "$directory" && lake cache stage mappings.jsonl "$out/$case-$workspace")
      done
    done
  '';
  check = pkgs.runCommand "lake-seed-check" { } ''
    ${common}
    export LAKE_CACHE_DIR="$TMPDIR/cache"
    mkdir -p "$out"
    for case in ${pkgs.lib.concatStringsSep " " cases}; do
      for workspace in ${workspaces}; do
        directory="$TMPDIR/cases/$case/$workspace"
        (cd "$directory" && lake cache unstage ${seed}/$case-$workspace)
        (cd "$directory" && lake build > build.log 2>&1) || { cat "$directory/build.log"; exit 1; }
        compiled=$(grep "Built " "$directory/build.log" | grep -cv "Built Belay\|Built SqliteVerifier" || true)
        echo "$case $workspace compiled=$compiled" >> "$out/result"
        if [ "$compiled" != 0 ]; then cat "$directory/build.log"; exit 1; fi
      done
    done
    cat "$out/result"
  '';
}
