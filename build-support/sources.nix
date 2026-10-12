# Select complete component inputs before converting any checkout path to the store.
{ lib, root ? ../. }:
let
  fs = lib.fileset;
  source = fileset: fs.toSource { inherit root fileset; };
  # Prune generated trees even when a developer creates them inside a component.
  clean = path: fs.unions (lib.mapAttrsToList (name: type:
    # `.belay` and `Generated` are tool-owned parts of proofs projects (ADR 0010).
    if builtins.elem name [ ".git" ".jj" ".lake" "build" "dist" "__pycache__" ".belay" "Generated" ] then fs.unions []
    else if type == "directory" then clean (path + "/${name}")
    else if type == "regular" then path + "/${name}" else fs.unions []) (builtins.readDir path));
  filtered = predicate: path: fs.intersection (clean path) (fs.fileFilter predicate path);
  extensions = names: filtered (file: builtins.any file.hasExt names);
  leanFiles = fs.unions [
    (fs.unions (map (name: root + "/${name}")
      (builtins.filter (name: lib.hasSuffix ".lean" name && name != "ConformanceRunner.lean"
        && (builtins.readDir root).${name} == "regular")
        (builtins.attrNames (builtins.readDir root)))))
    (extensions [ "lean" ] (root + /SqliteVerifier))
    (root + /lakefile.toml) (root + /lake-manifest.json) (root + /lean-toolchain)
  ];
  runtimeFiles = fs.unions [
    (extensions [ "py" ] (root + /migration_check))
    (extensions [ "py" ] (root + /belay/sqlite))
    (root + /LICENSE) (root + /docs/install.md)
    (root + /packaging/install.py) (root + /packaging/install.sh)
  ];
in {
  model = fs.toSource {
    root = root + /packages/belay-sqlite;
    fileset = fs.unions [
      (extensions [ "lean" ] (root + /packages/belay-sqlite/Belay))
      (root + /packages/belay-sqlite/lakefile.toml)
      (root + /packages/belay-sqlite/lake-manifest.json)
      (root + /packages/belay-sqlite/lean-toolchain)
    ];
  };
  runtime = source (fs.unions [ runtimeFiles
    (filtered (file: file.name != ".DS_Store" && !file.hasExt "pyc") (root + /examples)) ]);
  # The runtime without examples/: case seeds build against it, so a change to one example
  # rebuilds only that example's seed (ADR 0010 section 8).
  runtimeWithoutExamples = source runtimeFiles;
  lean = source leanFiles;
  conformanceLean = source (fs.unions [ leanFiles
    (root + /ConformanceRunner.lean) (extensions [ "lean" ] (root + /VerifierConformance)) ]);
}
