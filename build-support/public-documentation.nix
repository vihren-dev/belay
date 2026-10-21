# Check authored public documentation without adding tools to the proof runtime.
{ pkgs, leanToolchain, verifierLibrary, inventoryTools, docTools, modelPackage }:
pkgs.stdenv.mkDerivation {
  pname = "sqlite-verifier-public-documentation";
  version = "1";
  # The inventory reads the sources of the built packages below packages/.
  dontUnpack = true;
  nativeBuildInputs = [ leanToolchain pkgs.python3 ];
  dontConfigure = true;
  buildPhase = ''
    mkdir -p packages
    cp -R ${verifierLibrary} packages/sqlite-verifier
    cp -R ${modelPackage} packages/belay-sqlite-model
    export LEAN_PATH=${verifierLibrary}/.lake/build/lib/lean:${modelPackage}/.lake/build/lib/lean
    python3 ${inventoryTools}/tools/public_doc_inventory.py --root "$PWD" \
      --lean ${leanToolchain}/bin/lean --tools ${docTools} --output "$PWD/build/public-doc-inventory.json"
  '';
  installPhase = ''
    mkdir -p "$out"
    cp build/public-doc-inventory.json "$out/"
  '';
}
