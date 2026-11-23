# SQL reconstruction of computed schemas

Created 2026-11-19. DONE. [Issue 380](https://github.com/vihren-dev/belay/issues/380).

A caller can give #sql_check a computed schema that has no attached SQL
source. The checker can propose SQL for the tables, views, indexes and
triggers that the model supports. Table definitions retain keys, constraints,
defaults, generated expressions, collations and foreign keys. The SQL for
an index resolves column positions against its table. View and trigger bodies
retain the names and nested queries of their syntax. The text must quote
identifiers and literals so that SQLite parses the intended constructs.

Replay still checks exact catalog and row equality with constructionMatches
or constructionWithoutTriggersMatches. When the proposed SQL cannot recreate
the witness, the checker reports unknown. The existing text and time limits
apply to the generated construction.

## Acceptance

Exercise a computed schema with a key and an index through #sql_check. Parse
and run the emitted SQL for examples of each catalog entry, including nested
expressions, a partial index, table and column constraints, a generated
column, a view and a trigger. Check equality of the reconstructed model
database and replay representative cases with the pinned SQLite. Keep a
negative case where reconstruction fails and verify the diagnostic.

ReplayDatabaseSql emits the catalog definitions and stored rows. CheckSamples
uses this printer when a schema has no saved text. CheckReplayData checks
the resulting database before a replay can reach the user. CatalogView keeps
syntax and a separate subquery list. CatalogIndex and generated columns keep
resolved expressions. CatalogTable also keeps information about the spelling
of keys and past renames that affects later DDL.
