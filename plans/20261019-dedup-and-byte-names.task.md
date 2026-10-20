# Deduplication and identifiers as bytes (ADR 0013, step 8)

Created 2026-10-19. Status: DONE (pull requests #168 and #169).
Status file: [status](20261019-dedup-and-byte-names.status.md).
Specification: [ADR 0013](../docs/adr-0013-model-structure.md), "Order" step 8, the
implementation note of step 1 on folded names, and owner decision 9. Verdict: unchanged.

## Pull requests

Pull requests in the stack on step 7: the deduplication first, then identifiers as bytes,
which also rewrites the approved files of `examples/` and their hashes. None changes
`judge/` or `integrity/`.

## Outcome

1. **Byte helpers once.** `bytesBeforeNul`, ASCII lower-casing and keyword comparison exist
   once, used by `Json/` and `Date/`.
2. **One `json_valid` grammar.** `json_valid` and the other JSON readers parse a text once
   with one grammar; the strict (RFC 8259) check is a property of that parse, not a
   second parser.
3. **One path walker.** `Json/Path.lean`'s `lookupStep` and `Json/JsonbOffset.lean`'s
   `locateStep` are one walker over a JSON path.
4. **One printf front end.** `RealText.lean` and `Date/Printf.lean` share one front end
   over bytes, over the digit core they already share.
5. **Byte-string literals.** Keywords and fixed texts are written with a byte-string literal
   (a macro that elaborates to the `List UInt8` the kernel sees) instead of byte lists such
   as `[97, 117, 116, 111]`.
6. **Identifiers as bytes.** Table, column and index names are `List UInt8` in the Syntax
   IR, the catalog, the resolved statements, the codec and the public API; name lookups
   compare folded bytes. The CLI, the JSON wire format and messages show the same text as
   before.

## Tests

- `just test-full`, `just test-nix` and `just test-scheduled` pass after each pull
  request; the scheduled mutant suite kills every mutant, with anchors moved.
- The verdict of every corpus is unchanged, entry for entry, against step 7.
- `#guard` examples: the byte-string literal equals its byte list; each deduplicated
  function gives the results of the functions it replaces on their existing examples.
- Kernel time of the model suite and of one case, before and after identifiers as bytes.

## Key points

- **Approved files.** `examples/atuin/approved/` and `examples/constant_default/approved/`
  name tables and columns; with byte names they are rewritten and the gate's approved
  hashes change (owner decision 9).
- **Wire format.** The frontend writes names as JSON strings; the codec must keep that
  form, so names decode from strings to bytes.
- **Messages** print names; SQLite prints the bytes as written, which may be invalid UTF-8.
- **Kernel time** is the reason for outcome 6: measure it, as step 1's note did.
- **Mutants** anchored on name lookups and on the moved JSON and printf code move.
