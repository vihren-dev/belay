# Task: a user document for execution profiles (#19, one slice)

Created 2026-11-06. Issue: [#19](https://github.com/vihren-dev/belay/issues/19).
Status: [20261106-execution-profile-docs.status.md](20261106-execution-profile-docs.status.md).

## Problem

Issue #19 asks for user documentation that a reader can use without prior
knowledge of the design. Its last review names
[`docs/execution-profile.md`](../docs/execution-profile.md) as one document that
fails: it still uses the vocabulary of the removed verifier product (ADR 0021),
and it mixes three audiences.

Current errors and mixed content in the document:

- The first paragraph says that the supported version strings are `3.51.0` and
  `3.46.0` and that unsupported versions reject. No model code checks or reads
  `Profile.release`: it is recorded metadata.
  The model's profile is `Belay.Sqlite.Model.Profile`
  (`packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/Profile.lean`),
  and `Profile.pinned` is SQLite 3.51.0. The parser library has grammars for 24
  releases (`parser/dialects.json`, ADR 0029), which are syntax only. Some
  tests compare the model with native 3.46.0 (for example
  `tests/add_column_defaults_test.py`). The native-only 3.53.4 build records
  evidence only.
- "Without a migration framework", "approved contract" and "SQLx" belong to
  the removed product.
- The text says that configuration-changing SQL is unsupported. `Profile` now
  has `foreignKeys` and `recursiveTriggers`, the model implements both settings
  on and off, and `docs/semantic-subset.md` describes clock values and time
  zones.
- About half of the document (the sections "Native corpus profiles (ADR 0005,
  in progress)" and the 3.53.4 paragraph) describes the recorder, its transport
  format versions and refusals. That is for the team and designers, not for
  library users.

## Observable behavior when done

1. `docs/execution-profile.md` is a user document. A Lean user of the library
   learns from it:
   - what an execution profile is, and which fields of `Profile` and `Limits`
     resolution and execution read;
   - which SQLite release the model describes (`Profile.pinned`), how to make
     a profile for a measured build (`Profile.documented` or a full
     `Profile`), and what the other parser releases and the native-only 3.53.4
     build give and do not give;
   - the assumptions under which the model's results agree with SQLite (one
     connection, no other writers, no extensions, the outcomes that the model
     excludes, such as I/O errors and crashes);
   - the storage model at the level that a proof needs;
   - how to measure the engine build of an application's driver and compare it
     with the profile (the current "Measuring a workload's engine builds"
     section, kept and made clear).
2. The document has no ADR or slice numbers, no "approved contract",
   "migration framework" or "SQLx", and no recorder transport details. Each
   fact in it agrees with the current code; the implementer checks each fact
   against the code or the tests that it names.
3. The recorder content moves, with its meaning unchanged, to the team
   documentation of native records: `docs/native-corpus-format.md` or a new
   document beside it. Nothing that the recorder does is lost from the
   documentation.
4. Links into the moved content point to its new place. Today
   `docs/conformance-model.md` links to the anchor
   `execution-profile.md#native-corpus-profiles-adr-0005-in-progress`, and
   `docs/conformance-format-v2.md`, `docs/upstream-pilot.md` and
   `docs/lean-simplification-goal.md` link to the document.
5. The text follows the writing style of `CLAUDE.md`: one audience per
   document, short sentences, lists instead of long inline lists.

Out of scope: `docs/semantic-subset.md` (747 lines) and the other items of #19
are later slices. ADRs and historical plans keep their text.

## Tests

- `tests/docs_test.py` (`test_local_markdown_links`) checks that every local
  link resolves. It does not check anchors, so the implementer also searches
  the repository for links to the old anchor and fixes each one.
- A new unit test in `tests/docs_test.py` checks that
  `docs/execution-profile.md` has none of these terms: `ADR `, `approved
  contract`, `migration framework`, `SQLx`, `formatVersion`. This keeps the
  user document free of removed vocabulary and recorder details.
- The reviewer checks the facts (R19) and the audience split.

## Tricky points

- Keep the meaning of every sentence that moves. Where the old text is
  ambiguous, the issue says to ask the owner before a rewrite.
- The settings that the model implements and the settings that it does not
  are in `conformance/profile_scope.py`: `unsupported_setting` names IMMEDIATE
  transactions, read-only access, untrusted schema mode and other writers. The
  model implements foreign keys and recursive triggers on and off, and a
  controlled clock (`tests/profile_scope_test.py`). The paragraph of
  `docs/conformance-format-v2.md` that says "no foreign keys or recursive
  triggers" and "no controlled clock" is stale; correct it in the same slice.
- Resolution and execution do not read `Profile.release` or
  `Profile.sourceId`; they are recorded metadata that does not select or check
  the semantics. Do not claim a rejection of an unknown release. The surface runs statements with `Profile.pinned`
  (for example `packages/belay/Belay/Sqlite/Database.lean`), and its SQL terms
  parse with `Release.default`
  (`packages/belay-sqlite-text/Belay/Sqlite/Grammar.lean`), both 3.51.0.
