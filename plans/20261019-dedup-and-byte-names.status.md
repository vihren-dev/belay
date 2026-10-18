# Status: deduplication and identifiers as bytes (ADR 0013, step 8)

Created 2026-10-19. Status: open.
Task file: [task](20261019-dedup-and-byte-names.task.md).
Specification: [ADR 0013](../docs/adr-0013-model-structure.md), step 8, owner decision 9.

## Relevant files

- Bytes: `packages/belay-sqlite/Belay/Sqlite/Json/Bytes.lean`, `Json/Validity.lean`,
  `Date/Parse.lean`, `Date/Functions.lean`.
- JSON: `Json/Validity.lean`, `Json/Path.lean`, `Json/JsonbOffset.lean`.
- Printf: `RealText.lean`, `Date/Printf.lean`.
- Names: `Declarations.lean` (`normalizeIdentifier`), `Resolution/Syntax*.lean`,
  `Resolution/Catalog.lean`, `Codec/*.lean`, `packages/sqlite-verifier`, `examples/`.

## Progress

- 2026-10-19: duplicates mapped: `bytesBeforeNul` twice (`Json/Validity.lean`,
  `Date/Functions.lean`), ASCII lower-casing twice (`Json/Bytes.lean` `lowerAscii`,
  `Date/Parse.lean` `lowerAsciiByte`). Owner decision 9: identifiers as bytes in this step.

## Remaining

- All outcomes, checks, reviews, CI time, pull requests.
