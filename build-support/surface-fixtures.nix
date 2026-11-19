# Each suite declares the fixture modules its tests load. Follow local imports so an edit
# to a shared dependency rebuilds every suite that uses it. Fixture module names are unique
# across the tree, as required by tests/surface_support.py.
{ lib, root }:
let
  directory = root + /tests/surface;
  files = builtins.filter (path: lib.hasSuffix ".lean" (baseNameOf path))
    (lib.filesystem.listFilesRecursive directory);
  modules = builtins.listToAttrs (map (path: {
    name = lib.removeSuffix ".lean" (baseNameOf path);
    value = path;
  }) files);
  roots = builtins.fromJSON (builtins.readFile (root + /tests/surface_fixture_roots.json));
  # Surface fixtures import each local module on its own line.
  imports = path: lib.concatMap (line:
    let match = builtins.match "[[:space:]]*(public |private )?import ([[:alnum:]_]+)[[:space:]]*" line;
    in lib.optional (match != null && builtins.hasAttr (builtins.elemAt match 1) modules)
      (builtins.elemAt match 1)
  ) (lib.splitString "\n" (builtins.readFile path));
  resources = {
    SqlFileForms = [ (directory + /Frontend/Embedding/sql_files) ];
    SqlFileErrors = [ (directory + /Frontend/Embedding/sql_files) ];
    DerivedColumnOnSchema = [ (directory + /Schema/Tests/db) ];
    CheckRunSchemas = [ (directory + /Tooling/Tests/sql_files/customers.sql) ];
  };
in suite:
  assert lib.assertMsg (builtins.length files == builtins.length (builtins.attrNames modules))
    "Surface fixtures must have unique Lean module names across tests/surface.";
  let closure = builtins.genericClosure {
    startSet = map (key: { inherit key; }) roots.${suite};
    operator = item: map (key: { inherit key; }) (imports modules.${item.key});
  };
  in lib.concatMap (item: [ modules.${item.key} ] ++ (resources.${item.key} or [])) closure
