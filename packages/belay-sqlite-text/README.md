# belay-sqlite-text

The SQL text package below the surface (ADR 0016, D2, amended; ADR 0017, D2). It holds the
binding of the SQLite parser library (`Belay.Sqlite.ParserLibrary`, `Parse`, `ParseTree`,
`Grammar`, and the C shim in `c/`) and the translation of SQL text to the model's statement
syntax with the byte range of each node (`Belay.Sqlite.Translation`). The surface
(`packages/belay`) and the conformance harness use this translation.

The package requires only the model and imports only the model's roots and Lean's libraries.
Its modules are precompiled and linked with the parser library, whose folder Lake reads from the
environment variable `BELAY_PARSER_LIBRARY`:

```sh
nix-build build-support/default.nix -A parserLibrary.library --out-link build/parser-library
BELAY_PARSER_LIBRARY=$PWD/build/parser-library lake build BelaySqliteText BelaySqliteText:shared
```
