# The surface's untrusted sampler, pinned independently of the model and runner.
{ pkgs, leanToolchain }:
import ./lean-package.nix {
  inherit pkgs leanToolchain;
  pname = "plausible";
  directory = "packages/plausible";
  source = pkgs.fetchzip {
    url = "https://github.com/leanprover-community/plausible/archive/118aa17ee84656b8bd727fef7c458ee8c833385c.tar.gz";
    sha256 = "1y0jqfqqky4q7ry7pqdfg5vhayvdxn5jnslv4zs5vf1bmdlaf9py";
  };
  # Build with this repository's compiler; do not run the dependency's test suite.
  targets = [ "Plausible" "Plausible:shared" ];
}
