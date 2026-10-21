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
  # A Lean package under packages/: its Lean sources and its Lake files, relative to the package.
  package = directory: let folder = root + "/packages/${directory}"; in fs.toSource {
    root = folder;
    fileset = fs.unions ([ (extensions [ "lean" ] folder) ]
      ++ map (name: folder + "/${name}") [ "lakefile.toml" "lake-manifest.json" "lean-toolchain" ]);
  };
  runtimeFiles = fs.unions [
    (extensions [ "py" ] (root + /migration_check))
    (extensions [ "py" ] (root + /belay/sqlite))
    (root + /LICENSE) (root + /docs/install.md)
    (root + /packaging/install.py) (root + /packaging/install.sh)
  ];
in {
  model = fs.toSource {
    root = root + /packages/belay-sqlite-model;
    fileset = fs.unions [
      (extensions [ "lean" ] (root + /packages/belay-sqlite-model/Belay))
      (root + /packages/belay-sqlite-model/lakefile.toml)
      (root + /packages/belay-sqlite-model/lake-manifest.json)
      (root + /packages/belay-sqlite-model/lean-toolchain)
    ];
  };
  runtime = source (fs.unions [ runtimeFiles
    (filtered (file: file.name != ".DS_Store" && !file.hasExt "pyc") (root + /examples)) ]);
  # The runtime without examples/: case seeds build against it, so a change to one example
  # rebuilds only that example's seed (ADR 0010 section 8).
  runtimeWithoutExamples = source runtimeFiles;
  # The surface (ADR 0016, D1): its Lean files with its lakefile.lean, and the C shim that its
  # precompiled modules link with the parser library.
  surface = let folder = root + /packages/belay; in fs.toSource {
    root = folder;
    fileset = fs.unions [ (extensions [ "lean" ] folder) (folder + "/lake-manifest.json") (folder + "/lean-toolchain")
      (folder + "/c/parser_shim.c") ];
  };
  verifierLibrary = package "sqlite-verifier";
  verifierGate = package "verifier-gate";
  verifierConformance = package "verifier-conformance";
  docTools = package "public-doc-tools";
}
