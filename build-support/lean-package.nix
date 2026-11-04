# Build one Lean package under packages/ with Lake (ADR 0010 section 7, stage 1).
#
# The package builds in a copy of the repository layout: its sources at `directory` (for
# example packages/verifier-conformance) and the outputs of the packages it requires at their own
# paths (`requires` maps each path to a derivation). Lake replays those outputs without compiling, so each package compiles
# once, in its own derivation. The output is the package's Lake workspace: its sources, its
# Lake files and `.lake/build`, which a package or workspace that requires it replays.
# `extraSources` maps a path of the workspace to a source folder that is copied there: the files outside
# the package folders that a lakefile reaches by a relative path, for example the C of the parser
# library (ADR 0023). A package that replays the output of such a package passes the same set.
# `withoutSystemCompiler` removes the C compiler of the build environment from the PATH of Lake, so
# that the build proves that Lake compiles C with the Lean toolchain only (ADR 0023).
# `sharedRequires` names required packages whose shared libraries Lake links here, because the
# package's precompiled modules load them; the output keeps them beside its own in `.lake/build/lib`.
{ pkgs, leanToolchain, pname, directory, source, targets, requires ? { }, executables ? false, extraSources ? { }
, sharedRequires ? [ ], withoutSystemCompiler ? false }:
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
    ${lib.concatStrings (lib.mapAttrsToList (path: folder: ''
      mkdir -p "workspace/$(dirname ${path})"
      cp -R ${folder} "workspace/${path}"
    '') extraSources)}
    chmod -R u+w workspace
    cd "workspace/${directory}"
  '';
  buildPhase = ''
    export HOME="$TMPDIR"
    ${lib.optionalString withoutSystemCompiler ''
      kept=""
      IFS=:
      for folder in $PATH; do
        if [ "$folder" != "${leanToolchain}/bin" ] && { [ -e "$folder/cc" ] || [ -e "$folder/gcc" ] || [ -e "$folder/clang" ] || [ -e "$folder/c++" ]; }; then continue; fi
        kept="$kept:$folder"
      done
      unset IFS
      export PATH="''${kept#:}"
      for compiler in cc gcc c++ g++; do
        if command -v "$compiler" > /dev/null; then echo "$compiler is on the PATH of the build" >&2; exit 1; fi
      done
      case "$(command -v clang)" in "${leanToolchain}/bin/clang") ;; *) echo "clang is not the one of the Lean toolchain" >&2; exit 1 ;; esac
    ''}
    lake build --no-ansi ${lib.escapeShellArgs targets}
  '';
  installPhase = ''
    cp -R . "$out"
  '' + lib.concatStrings (map (path: ''
    find "$NIX_BUILD_TOP/workspace/${path}/.lake/build/lib" \
      -maxdepth 1 \( -name 'lib*.so' -o -name 'lib*.dylib' \) -exec cp {} "$out/.lake/build/lib/" \;
  '') sharedRequires);
})
