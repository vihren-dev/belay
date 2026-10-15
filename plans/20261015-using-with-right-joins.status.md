# Status: USING and NATURAL with RIGHT and FULL joins (slice 4d)

Created 2026-10-15. Status: IN PROGRESS.
Task: [task](20261015-using-with-right-joins.task.md).
Specification: [ADR 0012, Amendment 3, "Names with USING and NATURAL (slice 4d)"](../docs/adr-0012-query-semantics.md).

Relevant files: `packages/belay-sqlite/Belay/Sqlite/Resolution/Scope.lean`,
`Resolution/QueryExprs.lean`, `Resolution/JoinUsing.lean`, `Resolution/Sources.lean`,
`Resolution/Returning.lean`, `Resolution/Queries.lean`,
`Resolution/RestrictionText.lean`, `conformance/restriction_examples.py`,
`docs/semantic-subset.md`.

## Progress

- 2026-10-15: task and status files created. Native 3.51.0 checked for the rule of
  unqualified merged names over chains (right then full, full then right, full then
  inner, left then full), the REAL right column, the coalesce without affinity in
  `WHERE`, `GROUP BY` and `ORDER BY`, `*` of right and full joins, the coalesced left
  side of a later `USING`, and `ambiguous reference to a in USING()`.
- 2026-10-15: the model: `Source.mergeRule` and `Scope.resolveName` give an
  unqualified name its column, the right column or a coalesce
  (`Resolution/MergedNames.lean`, no affinity for a coalesce); `MergedLeft.lean`
  coalesces the left side of a generated condition when the `FROM` has a right or full
  join, with `ambiguous reference to a in USING()`; `using-with-right-join` leaves the
  registry. Proof `resolveName_single`: without right and full joins a name reads one
  column, as in slice 4b; the `mergeJoin` theorems state the slice 4b condition for a
  `FROM` without them. Found while recording: SQLite expands `t.*` of the left table to
  the merged name too (a native DISAGREE of the first version); the task's item 3 is
  corrected and `Scope.starOperand` follows SQLite's rule for `*` and `x.*`. The
  mutants of slices 4 and 4b follow the moved name resolution.
- 2026-10-15: review of the model commit (1 must, 1 should, fixed): explicit
  `NameResolution` cases in the `GROUP BY` terms; explicit statement cases in
  `MergedNameExamples.error`.
- 2026-10-15: 26 authored cases (`conformance/authored_merged.py`, all AGREE), six
  mutants (`conformance/merged_mutants.py`, in the write and join measurement), and the
  corpus 16 writer. A coalesce compared with an INTEGER column is the existing
  restriction `text-to-number`, as for any value without affinity; the chain cases join
  a column without a declared type.

## Remaining

- Full checks, CI time, PR A; then PR B (claim corpus 16, `mustAgree`).
