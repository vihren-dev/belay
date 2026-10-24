# Build one Lean package under packages/ with Lake (ADR 0010 section 7, stage 1).
#
# The package builds in a copy of the repository layout: its sources at `directory` (for
# example packages/verifier-conformance) and the outputs of the packages it requires at their own
# paths (`requires` maps each path to a derivation). Lake replays those outputs without compiling, so each package compiles
# once, in its own derivation. The output is the package's Lake workspace: its sources, its
# Lake files and `.lake/build`, which a package or workspace that requires it replays.
# `environment` adds variables to the build, for example the parser library that a lakefile reads.
# `sharedRequires` names required packages whose shared libraries Lake links here, because the
# package's precompiled modules load them; the output keeps them beside its own in `.lake/build/lib`.
{ pkgs, leanToolchain, pname, directory, source, targets, requires ? { }, executables ? false, environment ? { }
, sharedRequires ? [ ] }:
let
  lib = pkgs.lib;
  # Executables link against the C runtime libraries; on Linux the binaries need their store paths.
  linux = executables && pkgs.stdenv.hostPlatform.isLinux;
in pkgs.stdenv.mkDerivation ({
  inherit pname;
  version = "0.1.0";
  src = source;
  nativeBuildInputs = [ leanToolchain ] ++ lib.optional linux pkgs.autoPatchelfHook;
  buildInputs = lib.optionals linux [ pkgs.stdenv.cc.cc.lib pkgs.gmp pkgs.zlib ];
  preFixup = lib.optionalString linux ''
    addAutoPatchelfSearchPath ${leanToolchain}/lib
  '';
  dontConfigure = true;
  unpackPhase = ''
    mkdir -p "workspace/$(dirname ${directory})"
    cp -R "$src" "workspace/${directory}"
    ${lib.concatStrings (lib.mapAttrsToList (path: package: ''
      ${lib.optionalString (lib.hasPrefix "${directory}/" path) "chmod -R u+w \"workspace/${directory}\"\n"}mkdir -p "workspace/$(dirname ${path})"
      cp -R ${package} "workspace/${path}"
    '') requires)}
    chmod -R u+w workspace
    cd "workspace/${directory}"
  '';
  buildPhase = ''
    export HOME="$TMPDIR"
    lake build --no-ansi ${lib.escapeShellArgs targets}
  '';
  installPhase = ''
    cp -R . "$out"
  '' + lib.concatStrings (map (path: ''
    find "$NIX_BUILD_TOP/workspace/${path}/.lake/build/lib" \
      -maxdepth 1 \( -name 'lib*.so' -o -name 'lib*.dylib' \) -exec cp {} "$out/.lake/build/lib/" \;
  '') sharedRequires);
} // environment)
