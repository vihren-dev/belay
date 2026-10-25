# Guide correction: SQL source edits and importer rebuilds

Created 2026-10-24. Status: DONE. Published in private product PR #8.
Status: [progress](20261024-guide-sql-rebuilds.status.md).
Spec: [ADR 0017](../docs/adr-0017-user-surface.md), D6's accepted clarification
of 2026-10-24 and the S7 SQL-files task. The edited guide stays in the private
product repository; no private prose is copied into this public repository.

## Required outcome

The product guide must no longer promise that whitespace/comment edits cannot
rebuild importing modules, or that only the library that directly reads SQL
can rebuild. Source positions are editor metadata, but SQLite may retain
expression spelling as the output-column name. Such text is semantic data and
must remain in the elaborated term. Persistent source hashes and documentation
can also change compiled artifacts.

Explain native Lake input tracking and downstream artifact dependencies in
the SQL-file setup and stored-term descriptions. Keep the useful advice to
isolate SQL-reading modules in a small library and declare input_dir/input_file
with needs. Keep EOL normalization and the freshness checker. Make no custom
semantic-cache or unchanged-importer guarantee. The owner explicitly chose
this correction over deferring S7 for such a cache.

Preserve the published profile and Verso header corrections at product revision
17666ac9, and any reviewed S4 guide changes integrated before this correction.
Do not alter SQL examples, proof claims, section anchors or unrelated guide
behavior. The S7 implementation remains separately tracked; this correction
must not imply its elaborators/checker are already delivered.

## Validation and completion

Check the complete diff for only the affected explanatory paragraphs/comments.
Verify all fenced SQL bodies remain unchanged. A finite native probe using the
pinned SQLite 3.51.0 build must confirm that `SELECT 1+2`, `SELECT 1 + 2` and
`SELECT 1/*note*/+2` produce equal values but distinct column names. Preserve
the command, version and output in the private task status/evidence record.
This is documentation validation against native behavior, not a new model
conformance claim. No model, corpus, judge-lock or executable change is needed.

Use an isolated product workspace or the S4 guide owner's reserved workspace
after its current guide change, without concurrent edits. Record the private
task status and publish the correction as a coherent guide commit/PR, or in
the same guide branch when its ownership and review scope are explicit. Mark
both task/status DONE after publication. Follow the owner's temporary ban on
herdr review tabs before Monday, 2026-10-26 UTC; no tab is needed to do the work.
