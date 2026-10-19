# Status: deduplication and identifiers as bytes (ADR 0013, step 8)

Created 2026-10-19. Status: open.
Task file: [task](20261019-dedup-and-byte-names.task.md).
Specification: [ADR 0013](../docs/adr-0013-model-structure.md), step 8, owner decision 9.

## Relevant files

- Bytes: `packages/belay-sqlite/Belay/Sqlite/Json/Bytes.lean`, `Json/Read.lean`,
  `Date/Parse.lean`, `Date/Functions.lean`.
- JSON: `Json/Read.lean`, `Json/ReadScalar.lean`, `Json/Path.lean`, `Json/JsonbOffset.lean`.
- Printf: `RealText.lean`, `Date/Printf.lean`.
- Names: `Declarations.lean` (`normalizeIdentifier`), `Resolution/Syntax*.lean`,
  `Resolution/Catalog.lean`, `Codec/*.lean`, `packages/sqlite-verifier`, `examples/`.

## Progress

- 2026-10-19: duplicates mapped: `bytesBeforeNul` twice (`Json/Validity.lean`,
  `Date/Functions.lean`), ASCII lower-casing twice (`Json/Bytes.lean` `lowerAscii`,
  `Date/Parse.lean` `lowerAsciiByte`). Owner decision 9: identifiers as bytes in this step.
- 2026-10-19: `ByteText.lean` holds `lowerAscii`, `bytesBeforeNul`, `equalsKeyword` and the
  `bytes!` literal macro (outcomes 1 and 5); the twins in `Json/Bytes.lean`,
  `Json/Validity.lean`, `Date/Parse.lean` and `Date/Functions.lean` are gone, and the date
  keywords and units use the literal. The core has 132 modules. Verdict unchanged.
- 2026-10-19: one `json_valid` grammar (outcome 2). The reader records SQLite's
  `hasNonstd` flag (`ReadOutcome.value` and `ScalarRead` carry `standard`; `readJsonText`
  returns it), `standardJson` reads it, and `Json/Validity.lean` with its canonical grammar
  is gone. `slice` and `hexDigitsEnd` moved to `Json/Bytes.lean`. New guards for JSON5
  white space before separators and in nested values, checked with native 3.51.0. The core
  has 131 modules.
- 2026-10-19: one path walker (outcome 3). `lookupStep` in `Json/Path.lean` keeps the JSONB
  offsets (`LookupResult.found` holds a `LocatedNode`); `json_extract`, the arrows and
  `json_each` use it. `locateStep`, `locatePath` and `findMemberAt` are gone; `findMember`
  takes the offset. `Json/JsonbOffset.lean` keeps only the sizes and `LocatedNode`. The
  `json_last_duplicate_key` mutant follows `findMember`.
- 2026-10-19: one printf front end (outcome 4). `RealText.lean` holds the floating-point
  conversions over bytes: `decodeDouble` (with the `!` flag), `fixedDigitBytes`,
  `trimGeneralFraction`, `exponentSuffixBytes` and `formatGeneral`. `realText` is
  `formatGeneral 15 true` and returns bytes; `%J` is `formatGeneral 16 false`. The String
  copies (`finiteText`, `trimFraction`, `exponentSuffix`, `digitChar`, `digitAt`) and
  `formatGeneric16` are gone. `Date/Printf.lean` keeps `%d` and `%f`.

## Remaining

- Outcome 6; checks, reviews, CI time, pull requests.
