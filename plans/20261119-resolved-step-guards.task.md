# Execution guards for resolved schema statements

Created 2026-11-19. Open. [Belay issue 443](https://github.com/vihren-dev/belay/issues/443).

For a statement that resolves against the catalog of a valid database,
the resolver certificate supplies the catalog facts used by the execution
guards. Each CREATE targets the end of the catalog. CREATE INDEX and ADD
COLUMN refer to an existing table. A rename preserves the catalog outline.
DROP COLUMN satisfies both catalog checks in `Database.runsDropColumn`.
The database supplies one row store per catalog entry. The statement can
still fail a data constraint or reach a separate model restriction.

A caller of the CREATE TABLE and rewrite success laws, including the
corresponding `Sql.check_send` rules, can use a resolution equation and
validity without supplying the target position or the outline equality.
The raw step laws remain available. The schema success check accepts these
two resolved forms without computing either predicate on the catalog.

## Acceptance

Lean must check the guard proofs for arbitrary catalogs and shaped or valid
databases, with exactly the assumptions stated for each law. Compile surface
proofs that use the two send rules on abstract connections, the schema success
path, and the table-rebuild example. The example must prove success for the
same input rows without a local proof about rename resolution or outlines.
Run the repository's Nix test, verdict, infrastructure and scheduled checks.

## Existing contracts

`ResolverCertificate.link` takes validity of the current catalog.
`Resolved.Statement.SchemaLink` already describes the ADD COLUMN strict
default and the positions removed by DROP. Both facts have consumers.
`Database.runsDropColumn` reads the catalog only. `Model.step` has a
separate unmodeled result for an unsupported ADD COLUMN default.
