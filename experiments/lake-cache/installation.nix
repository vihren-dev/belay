# Experiment only: an installation whose Lean libraries are Lake packages (ADR 0010 section 3).
#
# Build with:
#   nix-build experiments/lake-cache/installation.nix --out-link build/lake-installation \
#     --extra-experimental-features 'nix-command flakes'
#
# It reuses the repository's own `leanRuntime` and `modelPackage` builds and adds
# what Lake needs to replay them instead of compiling: the `ir` outputs that the
# shipped runtime omits, a library-only `lakefile.toml` (no executables, no
# lean4export), and `enableArtifactCache = false`, because the outputs are read-only.
{ pkgs ? import ../../build-support/locked-nixpkgs.nix { system = builtins.currentSystem; }
, build ? import ../../build-support/default.nix { inherit pkgs; }
}:
let
  inherit (build) leanToolchain modelPackage sources;
  # The shipped runtime copies only `.lake/build/lib/lean`; keep `ir` as well.
  leanRuntimeWithIr = build.leanRuntime.overrideAttrs (old: {
    pname = "sqlite-verifier-lean-runtime-with-ir";
    installPhase = old.installPhase + ''
      cp -R .lake/build/ir "$out/.lake/build/"
    '';
  });
  libraryGlobs = ''["SqliteVerifier", "SqliteVerifier.Contract", "SqliteVerifier.ContractProofs", "SqliteVerifier.Library", "SqliteVerifier.NullableProjection", "SqliteVerifier.ApplicationKeys", "SqliteVerifier.ApplicationKeyPreservation"]'';
in pkgs.runCommand "sqlite-verifier-lake-installation" { } ''
  mkdir -p "$out/packages/sqlite-verifier" "$out/packages/belay-sqlite"

  cp -R ${modelPackage}/. "$out/packages/belay-sqlite/"
  chmod -R u+w "$out/packages/belay-sqlite"
  sed -i '/^defaultTargets/a enableArtifactCache = false' "$out/packages/belay-sqlite/lakefile.toml"

  library="$out/packages/sqlite-verifier"
  cp -R ${sources.lean}/SqliteVerifier ${sources.lean}/SqliteVerifier.lean ${sources.lean}/lean-toolchain "$library/"
  mkdir -p "$library/.lake/build/lib"
  cp -R ${leanRuntimeWithIr}/.lake/build/lib/lean "$library/.lake/build/lib/"
  cp -R ${leanRuntimeWithIr}/.lake/build/ir "$library/.lake/build/"
  cat > "$library/lakefile.toml" <<'EOF'
  name = "sqliteVerifier"
  version = "0.1.0"
  enableArtifactCache = false

  [[require]]
  name = "belaySqlite"
  path = "../belay-sqlite"

  [[lean_lib]]
  name = "SqliteVerifier"
  roots = []
  globs = ${libraryGlobs}
  EOF
  sed -i 's/^  //' "$library/lakefile.toml"

  mkdir -p "$out/bin"
  cp ${leanRuntimeWithIr}/.lake/build/bin/* "$out/bin/"
  ln -s ${leanToolchain} "$out/lean"
  chmod -R a-w "$out"
''
