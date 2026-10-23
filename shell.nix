# The development shell that .envrc loads: the packages of nix/dev-shell.nix, which the
# flake dev shell also has, plus the pinned Lean toolchain and the parser library of the Nix
# builds, so that a local `lake build` (just dev-build) uses the same Lean and links the same
# parser.
{ system ? builtins.currentSystem }:
let
  pkgs = import ./build-support/locked-nixpkgs.nix { inherit system; };
  native = import ./nix/sqlite.nix { inherit pkgs; };
  # The same derivations, and so the same store paths, as the Nix builds use.
  build = import ./build-support/default.nix { inherit system pkgs native; };
  leanToolchain = build.leanToolchain;
  shell = import ./nix/dev-shell.nix { inherit pkgs native system; };
  linux = pkgs.stdenv.hostPlatform.isLinux;
  # Lake compiles and links with the toolchain's bundled clang. That clang links for the
  # loader /lib64/ld-linux-x86-64.so.2, which NixOS does not have. With LEAN_CC set, Lake
  # calls this script instead and no longer adds the toolchain's own flags, so the script
  # adds them back: for a compile (-c), the sysroot and the bundled C headers; for a link,
  # the sysroot, lld, the bundled glibc stubs and unwinder, and the Nix loader.
  # A Lean upgrade can change these flags; a failed local build of an executable shows it.
  leanCc = pkgs.writeShellScript "lean-cc" ''
    toolchain=${leanToolchain}
    for argument in "$@"; do
      if [ "$argument" = -c ]; then
        exec "$toolchain/bin/clang" --sysroot "$toolchain" -nostdinc \
          -isystem "$toolchain/include/clang" "$@"
      fi
    done
    exec "$toolchain/bin/clang" --sysroot "$toolchain" -fuse-ld=lld \
      -L"$toolchain/lib" -L"$toolchain/lib/glibc" "$@" \
      "$toolchain/lib/glibc/libc_nonshared.a" "$toolchain/lib/glibc/libpthread_nonshared.a" \
      -Wl,--as-needed -Wl,-Bstatic -lunwind -Wl,-Bdynamic -Wl,--no-as-needed \
      -Wl,--dynamic-linker=${pkgs.stdenv.cc.bintools.dynamicLinker}
  '';
in
pkgs.mkShell ({
  packages = shell.packages ++ [ leanToolchain ];
  # The text package's lakefile reads it when Lake loads the package, as its Nix build does.
  BELAY_PARSER_LIBRARY = "${build.parserLibrary.library}";
} // shell.environment // pkgs.lib.optionalAttrs linux { LEAN_CC = "${leanCc}"; })
