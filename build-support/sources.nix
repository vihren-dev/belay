# Select complete component inputs before converting any checkout path to the store.
{ lib, root ? ../. }:
let
  fs = lib.fileset;
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
  # The surface (ADR 0016, D1): its Lean files with its lakefile.lean.
  surface = let folder = root + /packages/belay; in fs.toSource {
    root = folder;
    fileset = fs.unions [ (extensions [ "lean" ] folder) (folder + "/lake-manifest.json") (folder + "/lean-toolchain") ];
  };
  # The text package below the surface (ADR 0016, D2, amended): its Lean files with its
  # lakefile.lean, and the C shim that its precompiled modules link with the parser library.
  # The parser's C is `parser` below.
  text = let folder = root + /packages/belay-sqlite-text; in fs.toSource {
    root = folder;
    fileset = fs.unions [ (extensions [ "lean" ] folder) (folder + "/lake-manifest.json") (folder + "/lean-toolchain")
      (folder + "/c/parser_shim.c") ];
  };
  # The C of the parser library that Lake compiles into the text package (ADR 0023, D2), with the
  # layout of `parser/` in the repository: the committed generated C of each parser and tokenizer
  # (ADR 0029), the C library headers and the library's own files.
  # The text package, and each package that replays it, finds this folder at `../../parser`.
  parser = let folder = root + /parser; in fs.toSource {
    root = folder;
    fileset = fs.unions ([ (folder + /generated) (folder + /c-headers) ]
      ++ map (name: folder + "/${name}") [ "library.c" "library.h" "runtime.h" "tokenizer.c" "library_prefix.h"
        "library_tokenizer.c" "library_parser.c" "library_grammar.c" ]);
  };
  verifierConformance = package "verifier-conformance";
  docTools = package "public-doc-tools";
}
