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

## Catalog integration base

The catalog workspace merges the reviewed metadata head `c0e288b5` with published
PR #248, `e3d6aa38`. Its production packages are byte-identical to `c0e288b5`;
the published parent supplies the S6 and proof-cost prototype test registrations.
The two query-source status conflicts retain the newer acceptance records and
the retained S4 archive paths. The Nix foundation evidence above is unchanged.
No catalog or evaluator behavior changes in this integration commit.
Independent review `20261024T210803Z-63bcea9d` found no findings.

## Foundation: unresolved view catalog

The catalog now stores a view's written query, optional column names and indexed
expression subqueries. It retains names through catalog drops. A view occupies
the shared table/index namespace and has no stored rows. Catalog validity permits
missing references and cycles in the unresolved definition. The generic append
and drop laws cover the new catalog entry.

This is an interim catalog unit. CREATE/DROP VIEW syntax and query expansion are
not implemented yet. A manually supplied view is explicitly unmodeled at source,
write, trigger, index, ADD COLUMN, DROP TABLE and table-info boundaries that need
the later view handling. These paths do not invent a missing-table error or an
empty metadata result. Foreign-key listing and check pragmas use the catalog
object without expanding its SELECT. An existing view produces the native
view-name collision for CREATE TABLE and shared-name collision for CREATE INDEX.

The FK parent lookup distinguishes an absent name from an existing view: the
latter is a position-bearing mismatch, even when the view body cannot resolve.
The parent-schema frame therefore preserves the optional view position when no
physical parent exists; view bodies remain unrestricted. The selected mapping,
NULL, affinity, collation and action formulas are unchanged. The coordinated FK
proof closure adds only the new non-table cases. The exact retained-table lookup
law in `CatalogValidDrop` and its caller are carried from checked FK source
`135b8338948d9b3737c236f765e6fb2c841a6131`.

Missing-source laws now require view absence. Pragma-function laws require that
neither a table nor a view shadows the function. The maintained balance fixture
handles both shadowing cases while retaining the physical-ledger premise and all
SQL/data guards. The private guide mirror is deferred to the final installed
integration artifact; no private content is carried here.

`ClaimsViewCatalog.lean` checks manually supplied definitions, catalog positions,
row shape, name collisions, FK mismatch, conservative expansion boundaries and
pragma behavior through the public predicates. The selected surface suite also
checks the complete balance proof, arbitrary callback consumers and all nine FK
fixtures. The conformance loader and table comparator keep view storage empty;
their existing observations still describe physical tables, not view definitions.

The focused Nix check passed all 28 selected cases, with 53 deselected, in 57.17
seconds:
`/nix/store/lvbs6wdb1ck7bpxy746plv8a5h1q7xxl-sqlite-verifier-test-view-catalog-1`.
Nix predictions at
`/nix/store/d0szrxzshhfncprggija4qdjhps7xczq-sqlite-verifier-predictions`
are byte-identical to the accepted CTE baseline: all 53 files and 7,372 cases,
zero changed records. The logs and comparison are retained under
`build/agent-logs/view-catalog/`. Full view-part acceptance remains pending;
this checked foundation does not complete part 3.

Review `20261024T214402Z-59dc5215` found no findings but disclosed incomplete
file coverage. Supplementary review `20261024T214759Z-59dc5215` inspected all
77 changed files and found three stale mutation anchors. The follow-up preserves
the new view branches while restoring the existing CREATE TABLE, missing-table
ADD COLUMN and DROP TABLE IF EXISTS mutations. A static audit also found two
stale derived-column affinity/collation anchors from the metadata foundation;
the same follow-up restores those mutations without changing their targets.
All five named Nix mutant checks passed, one selected mutant per invocation.
Each retained the existing unchanged-model agreement and mutant-kill assertions.
The disposable selection changes the existing dictionary in place, including the
resolver runner's captured default; it adds no permanent runner or test.

- `no_table_exists`: `/nix/store/ly18lnjdlqqbzwgwf2av057hyhlab084-sqlite-verifier-test-view-catalog-mutant-no_table_exists-1`.
- `no_such_table`: `/nix/store/2sqxk6736i6v4lc8g0ahwq6zsmji8n4p-sqlite-verifier-test-view-catalog-mutant-no_such_table-1`.
- `if_exists_reports_missing`: `/nix/store/p922y6qblmf5pwdsflvy2fvyx43ap74x-sqlite-verifier-test-view-catalog-mutant-if_exists_reports_missing-1`.
- `source_affinity_lost`: `/nix/store/ww4csy3i19viqg04nj0jbvv6z505crb6-sqlite-verifier-test-view-catalog-mutant-source_affinity_lost-1`.
- `source_collation_lost`: `/nix/store/5wslqf8vgvzrkbhrfkrkb0h3b4dzjma9-sqlite-verifier-test-view-catalog-mutant-source_collation_lost-1`.

Logs and the exact disposable selection are retained under
`build/agent-logs/view-catalog/`. No model or proof definition changes in this repair.

Repair source `a890097fe76f92529517393bd5ba904f1a8853d9` passed independent
review `20261024T215844Z-a890097f` with zero must and zero should findings.
The catalog foundation and its five mutation repairs are now checked and reviewed.

## Remaining view scope

CREATE/DROP VIEW, late and closed source lookup,
cycles, view metadata before compound rewrites, pragma metadata, write errors and catalog/
statement preservation remain OPEN under the existing task. FK proof leaves are
coordinated with their owner before mechanical view-case extensions. Frozen v53
remains unpublished and mutable in the separate evidence workspace. No corpus,
claim or judge-lock file changes in the foundation.
