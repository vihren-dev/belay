# Trial development shell for ADR 0020: the tools of nix/flake.nix's dev shell, plus the
# pinned Lean toolchain of the Nix builds, so that a local `lake build` uses the same Lean.
# Enter it with `nix-shell`, or with direnv and `use nix` in .envrc.
{ system ? builtins.currentSystem }:
let
  pkgs = import ./build-support/locked-nixpkgs.nix { inherit system; };
  native = import ./nix/sqlite.nix { inherit pkgs; };
  # The same derivation, and so the same store path, as the toolchain of the Nix builds.
  leanToolchain = (import ./build-support/default.nix { inherit system pkgs native; }).leanToolchain;
  testPython = pkgs.python3.withPackages (ps: [ ps.pytest ps.hypothesis ]);
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
  packages = [ pkgs.just pkgs.coreutils testPython native.sqlite native.sqlite346 native.sqlite3534
               leanToolchain pkgs.rsync ]
    ++ pkgs.lib.optionals linux [ pkgs.patchelf ];
  SQLITE_VERIFIER_SHELL = "default";
  SQLITE_VERIFIER_SYSTEM = system;
  SQLITE_VERIFIER_PYTHON = "${pkgs.python3}/bin/python3";
} // pkgs.lib.optionalAttrs linux { LEAN_CC = "${leanCc}"; })
