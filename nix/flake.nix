{
  description = "SQLite migration verifier development environment";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [ "aarch64-darwin" "x86_64-linux" ];
      forSystems = nixpkgs.lib.genAttrs systems;
      packagesFor = system:
        let pkgs = import nixpkgs { inherit system; };
        in { inherit pkgs; } // import ./sqlite.nix { inherit pkgs; };
    in {
      packages = forSystems (system: { inherit (packagesFor system) sqlite sqlite346 sqlite3534; });
      checks = forSystems (system:
        let native = packagesFor system;
        in (import ../build-support/default.nix {
          inherit system native;
          inherit (native) pkgs;
        }).tests);
      devShells = forSystems (system:
        let
          tools = packagesFor system;
          shell = import ./dev-shell.nix { inherit system; inherit (tools) pkgs; native = tools; };
        in {
          default = tools.pkgs.mkShell ({ inherit (shell) packages; } // shell.environment);
        });
    };
}
