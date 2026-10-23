# The packages and environment variables of the development shell. The flake dev shell
# (flake.nix, which CI enters) and the root shell.nix (which direnv loads) both take them
# from here, so that the two shells cannot drift apart. shell.nix adds the Lean toolchain.
{ pkgs, native, system }:
{
  packages = [
    pkgs.just
    pkgs.coreutils
    (pkgs.python3.withPackages (ps: [ ps.pytest ps.hypothesis ]))
    native.sqlite
    native.sqlite346
    native.sqlite3534
  ] ++ pkgs.lib.optionals pkgs.stdenv.hostPlatform.isLinux [ pkgs.patchelf ];
  environment = {
    SQLITE_VERIFIER_SHELL = "default";
    SQLITE_VERIFIER_SYSTEM = system;
    SQLITE_VERIFIER_PYTHON = "${pkgs.python3}/bin/python3";
  };
}
