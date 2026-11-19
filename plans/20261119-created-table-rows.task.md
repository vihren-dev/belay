# Empty rows of a table created by a script

Created 2026-11-19. Open. [Issue 445](https://github.com/vihren-dev/belay/issues/445).

If a statement resolves to CREATE TABLE and its step continues, the new
position holds exactly the resolved table shape and an empty row list.
An IF NOT EXISTS no-op resolves as an empty drop and gives no such fact.

In a mixed-script success proof, a caller can use a table created at an
earlier step as an empty copy destination while the intervening statements
preserve it. The existing table frame determines when that guarantee ends
and how the position moves after a drop. The rebuild example must prove the
same success claim using this library fact, without keeping its own empty-row
invariant or calculating the length of the catalog.

## Acceptance

Compile the step theorem on an arbitrary connection. Use the mixed-script law
in the README rebuild proof. Check a prefix containing two new tables, an edit
that preserves one and may change the other, and a CREATE TABLE IF NOT EXISTS
that resolves as a no-op. Run the model and surface package builds, the
rebuild suite and the repository acceptance checks.
