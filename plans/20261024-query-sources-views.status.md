# Status: query-source views

Created 2026-10-24. Part 3 OPEN; the overall query-source task remains OPEN.
Task: [queries as sources](20261024-query-sources.task.md).
Main status: [accepted parts and publication](20261024-query-sources.status.md).
Specs: ADR 0019 D5/slice 4 and ADR 0017 S6.

## Foundation: declared-type origins

The foundation retains the declared-type origin of each resolved result column
separately from its expression affinity and collation. SQLite's `columnTypeImpl`
follows physical columns, derived columns and scalar subqueries; a compound
follows its right-most term. CAST, COLLATE, unary plus and a full-join coalesce
have no declared-column origin. RIGHT JOIN's merged output follows the right
column. This is metadata needed by view column descriptions, not view DDL.

The existing source resolver and scalar shapes carry that metadata. No evaluator,
CatalogEntry constructor, SQL form or FK definition changes in this unit.
Normalized view column types remain separate work: native evidence distinguishes
SQLite's FLEXNUM metadata from ordinary NUMERIC, including through nested views.
The foundation does not approximate those types with a copied declaration.

Kernel examples cover all columns of a star, absent declarations, expression
wrappers, INTEGER/REAL compounds, nested derived columns, LEFT/RIGHT/FULL merged
outputs, scalar subqueries and the complete indexed resolver. The existing
physical-column query proofs carry the additional origin in their shape
premises; their conclusions and the S4 physical-table premises are unchanged.

The descendant also carries the published PR #248 CTE acceptance/status text and
ADR implementation paragraph from `e3d6aa388eeb070b94cdcf34a474f79f692d3c12`.
The full publication ancestry will be merged at a later clean boundary.
The focused Nix surface check passed all 17 selected fixtures (55 deselected)
at `/nix/store/zqx7vb0nvvhp89fvx34ncpcfjh2wy2g4-sqlite-verifier-test-view-column-origins-1`.
It includes the physical-column IN claims, source/CTE consumers and the complete
balance success proof. The model package build checks the origin kernel examples.
Nix predictions at
`/nix/store/kdphp0hd50xm2cp21b8xkir65cjhylwh-sqlite-verifier-predictions`
match the accepted CTE baseline
`/nix/store/wbpwn1x38fyn3l0g00wg5m011n6ajwq4-sqlite-verifier-predictions`
byte-for-byte: all 53 files and 7,372 cases, with zero changed records.
The exact comparison is retained in
`build/agent-logs/view-column-origin-prediction-changes.json`.
Independent review of this checked unit follows its commit.

## Remaining view scope

CREATE/DROP VIEW, unresolved catalog definitions, late and closed source lookup,
cycles, normalized column metadata, pragma metadata, write errors and catalog/
statement preservation remain OPEN under the existing task. FK proof leaves are
coordinated with their owner before mechanical view-case extensions. Frozen v53
remains unpublished and mutable in the separate evidence workspace. No corpus,
claim or judge-lock file changes in the foundation.
