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
The normalization unit below handles native evidence that distinguishes
SQLite's FLEXNUM metadata from ordinary NUMERIC, including through nested views.
Origins alone do not approximate those types with a copied declaration.

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
Independent review `20261024T203741Z-86e15af9` found zero musts and two shoulds:
enumerate the remaining star-operand constructors and wrap the compound-shape
docstring. Both are corrected in the normalization descendant below.

## Foundation: normalized source declarations

This unit computes normalized declarations separately from origins and
expression affinities. It preserves a declared spelling when affinity agrees;
otherwise it selects SQLite's INT, REAL, TEXT, BLOB or NUM spelling. Expressions
without affinity have no declaration. A physical untyped column has BLOB
affinity and therefore normalizes to BLOB.

Compound declarations use the left-most origin and the effective source
affinity. Expression origins still follow the right-most term. A metadata flag
retains SQLite's FLEXNUM distinction through derived sources, scalar shapes,
COLLATE and stars. A first-term CAST with a retained numeric compound affinity
sets that flag; a text conflict that changes affinity to BLOB clears it.
The numeric Value operations, comparison affinities and evaluator are unchanged.

Kernel examples distinguish direct INTEGER/REAL compounds from enclosing
queries, original declarations from canonical names, wrappers and untyped
columns, and nested FLEXNUM from ordinary NUMERIC despite their equal NUM
spelling. Existing scalar-query proof premises for physical tables remain the
same: a small law proves their expressions cannot inherit a FLEXNUM flag when
the scope has no resolved subqueries.

The focused Nix check passed all 17 selected fixtures (55 deselected) in 44.53
seconds, including the complete balance proof and physical-column IN claims:
`/nix/store/yy0xf2n1yrg9assy7y31bfda0v6ign9q-sqlite-verifier-test-view-column-types-1`.
Its model dependency checks the new normalization examples in the kernel.
Nix predictions at
`/nix/store/50ck3gadmqmjl6yp9s4mz03f3da1bim9-sqlite-verifier-predictions`
match the accepted CTE baseline above byte-for-byte: all 53 files and 7,372
cases, with zero changed records. The exact comparison and Nix logs are retained
under `build/agent-logs/view-column-types/`. Independent review
`20261024T210304Z-858e0a2b` found zero musts and zero shoulds. The checked source
is `858e0a2b14c0457c378edd7b2bd9e85af26ed5c0`.

## Remaining view scope

CREATE/DROP VIEW, unresolved catalog definitions, late and closed source lookup,
cycles, view metadata before compound rewrites, pragma metadata, write errors and catalog/
statement preservation remain OPEN under the existing task. FK proof leaves are
coordinated with their owner before mechanical view-case extensions. Frozen v53
remains unpublished and mutable in the separate evidence workspace. No corpus,
claim or judge-lock file changes in the foundation.
