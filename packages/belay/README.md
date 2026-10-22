# belay

The surface: the library that Lean developers import, `Belay`, with the SQLite surface under
`Belay.Sqlite` (ADR 0016). It imports the model only through its roots, `Belay.Sqlite.Model`,
`Belay.Sqlite.Model.Codec` and `Belay.Sqlite.Model.Codec.Resolution` (the terms of statement
syntax that `sql r"..."` gives), and reads SQL text with the text package below it,
`packages/belay-sqlite-text`.

The text package calls the SQLite parser library while a file elaborates, so the modules of
both packages are precompiled and linked with the library. Lake reads the library's folder from
the environment variable `BELAY_PARSER_LIBRARY`:

```sh
nix-build build-support/default.nix -A parserLibrary.library --out-link build/parser-library
BELAY_PARSER_LIBRARY=$PWD/build/parser-library lake build Belay Belay:shared
```

Lake loads the precompiled modules for `lake build`, `lake lean FILE` and the editor's server.
`lake env lean FILE` does not load them, and `lean` then stops at the first parser call.
