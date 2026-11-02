# belay-sqlite-text

The SQL text package below the surface (ADR 0016, D2, amended; ADR 0017, D2). It holds the
binding of the SQLite parser library (`Belay.Sqlite.ParserLibrary`, `Parse`, `ParseTree`,
`Grammar`, and the C shim in `c/`) and the translation of SQL text to the model's statement
syntax with the byte range of each node (`Belay.Sqlite.Translation`). The surface
(`packages/belay`) and the conformance harness, through the package's program, use this
translation.

The package requires only the model and imports only the model's roots and Lean's libraries.
Its modules are precompiled and linked with the parser library. Lake compiles the library's C code
itself, from the files under `parser/` of this repository (ADR 0023): a `lake build` needs the
pinned Lean and no system C compiler, no C library headers and no Nix.

```sh
lake build BelaySqliteText BelaySqliteText:shared
```

The program `belay-sqlite-translate` translates a batch of SQL texts for the conformance
harness. It reads one JSON request on each line of standard input and writes one JSON answer
line for each; `Belay/Sqlite/TranslationRequest.lean` describes both. The conformance runtime
contains it at `.lake/build/bin/belay-sqlite-translate`:

```sh
lake build belay-sqlite-translate
```

The lakefile reaches `parser/` by the path `../../parser`, so the package folder must stay two
levels below the repository folder. The C under `parser/generated/` comes from Nix: after a change
to `parser/dialects.json`, to a vendored SQLite release or to a generator, run `just parser-sources`
and commit the result.
