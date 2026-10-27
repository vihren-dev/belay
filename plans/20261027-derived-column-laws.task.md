# Derived-column migration laws: general laws in the packages, the guide example as fixtures

Created 2026-10-27. Status: OPEN.
Status: [progress](20261027-derived-column-laws.status.md).
Specs: [ADR 0017](../docs/adr-0017-user-surface.md), S6 and S8;
[S6 automation](20261024-s6-automation.task.md), the paragraph on the two guide
claims that are proved outside that task, and its part 2 open point 5 in the
[status file](20261024-s6-automation.status.md);
[migration patterns](20261024-s6-migration-patterns.task.md) and the section
"Owner decision on the example modules (2026-10-26)" of its
[status file](20261024-s6-migration-patterns.status.md).

## Purpose and boundary

The guide's migration example adds a column that holds a value derived from
other columns of the same row, fills it, and moves a lookup to the new column:

```sql
ALTER TABLE items ADD COLUMN name_lower TEXT;
UPDATE items SET name_lower = lower(name);
-- before: SELECT ... FROM items WHERE lower(name) = lower(?1)
-- after:  SELECT ... FROM items WHERE name_lower = lower(?1)
```

Sixteen `NormalizedField*` modules (13 in `belay-sqlite-model`, 3 in `belay`,
about 1,900 lines) prove this example. They are general in table and column
names, but they fix the derived expression to `lower` of one source column
(of any affinity), stored in an appended TEXT column, and
the `belay` modules fix the four-statement expansion script of the guide (the
column, the backfill, two triggers), its plan and its lookup simulation. Two
owner decisions apply:

- 2026-10-26: guide examples are not part of the model or the surface. The
  general content stays under general names. The example-specific parts (the
  plan, the lookup simulation, the expansion theorem) move to `tests/surface`.
- 2026-10-27: each new or kept theorem, lemma and `Prop` is stated as generally
  as the proof allows at a reasonable cost, so other cases can use it.

The guide's migration query claim is proved today for one concrete database
(`tests/surface/S6RulesQueryPattern.lean`). This task also proves it for every
admitted database of a site (S6 automation part 2, open point 5).

This task changes no SQL meaning, no execution, no prediction, no corpus, no
claim and no judge file.

## Required outcomes

- **No package code is named after the example.** No module, namespace or
  declaration under `packages/` has `NormalizedField` in its name. Each kept
  law is in a module named by what it states. Old names are deleted, not
  aliased (repository rule "Replaced code"); all callers move to the new names.
- **Existing general laws are kept once.** The declarations of these modules
  that are already general (for example the successful plain UPDATE effect, the
  ADD COLUMN and CREATE TRIGGER steps, the catalog lookups after ADD COLUMN and
  CREATE TRIGGER, the resolution of an identifier and of a one-table SELECT, the
  calm-statement facts, the step output of a simple query, generated cells of a
  table with no generated column) move to general modules. Where an existing
  law elsewhere states the same fact (for example `Catalog.findTable_addColumn`,
  `addColumn_database`, `Query.simple_results_append`), the callers use the
  existing law and the copy is deleted.
- **The backfill law is general over the derived expression.** For any table
  and any appended column, a successful plain UPDATE that assigns to that
  column the value of an expression over the other columns of the row reaches
  the database whose rows are the old rows with the stored value of the
  expression appended. The premises are explicit: for example the expression
  reads only the old columns, has no subquery, no parameter-dependent or
  nondeterministic part (or the law takes the parameters as given), and
  evaluates without a fault on every row; no trigger fires. "Stored value" is
  the value after the column affinity. `lower` of one column into a TEXT column is one
  instance; the stability of its value under TEXT affinity is the instance of
  the affinity premise.
- **The scan law is general over row maps.** The full scan of a table whose
  rows are mapped by a function that keeps each rowid and the sort key equals
  the old scan with the same map applied (the stable-sort-commutes-with-map
  law). No law of this kind exists today outside these modules.
- **The lookup laws are general over the derived expression and the probe.**
  For any one-table simple query whose condition is `e = p` (with `e` the
  derived expression and `p` a probe expression that does not read the row), the
  rows before the migration equal the rows after it with the condition `c = p`
  (`c` the appended column), and also the rows after it with the unchanged
  condition. The premises state when the stored value compares with `p` as the
  value of `e` does: affinity and collation of both comparisons, as the
  NOT IN task's value law does. The laws reuse `Query.simple_results_append`
  where it applies. That law cannot cover a condition that reads the appended
  column; the private filter-agreement lemma of `NormalizedFieldQueries`
  (any two conditions that agree on each old row and its extended row give
  the same results) covers it and is general content to keep.
- **The surface has the general migration statement.** A `belay` statement
  relates the lookups before and after the migration "add a column, backfill it
  from an expression", as the relation that the guide uses, over a site
  structure whose premises are general (the table and columns exist, the
  premises of the laws above). Whether the expansion with triggers has a
  general surface statement is the implementer's choice under the 2026-10-27
  rule; the guide's two concrete triggers do not go into a package.
- **The example parts are fixtures.** The four-statement expansion script, its
  plan, the lookup simulation and the expansion theorem live in `tests/surface`
  and are proved from the general laws, with the guide's `lower`. Package code
  that depends on them today (`SendSuccessIfOk.ifOk_send_expansion`) moves with
  them or becomes general.
- **The universal migration query claim is proved.** In `tests/surface`, next
  to `S6RulesQueryPattern.lean`, a theorem proves the guide's migration query
  claim for every admitted database of a site and every bound value, from the
  general laws. The concrete-database claim and the native counter refutation
  (`MigrationExpansionCounter.lean`) stay. The status file records what the
  guide statement needs (its premises).

## Tests and acceptance

- The existing fixtures keep their meaning after the move:
  `NormalizedFieldLaws.lean`, `NormalizedFieldExpansionLaws.lean`, the
  `Application*` and `ExpansionCount*` fixtures and
  `GlobalSignupInvariant.lean`. They may be renamed. Each axiom audit allows
  only `propext`, `Classical.choice` and `Quot.sound`. A changed audit count is
  explained in the status file.
- Kernel examples show that the general laws apply beyond the guide: at least
  one derived expression other than `lower` of one column (for example a
  concatenation of two columns, or an integer expression into an INTEGER
  column), and one example where an affinity premise fails and the lookups
  differ.
- Native SQLite checks the concrete query results that those examples state,
  with the native helpers of the surface tests.
- The universal claim has an axiom audit through its pytest driver.
- All prediction files stay byte-identical to the base (`nix-build
  integrity/judge.nix -A predictions`, 55 files).

One acceptance part: each coherent commit gets focused checks, dev-build and
independent review. After the last review: `just dev-build`, then `just
test-full` and `just verdict`; at task end, `just test-nix` and `just
test-scheduled-checks`. Only Nix results are acceptance evidence.

## Existing interfaces and tricky points

- A read-only map of the 16 modules (declarations, kinds, importers,
  duplicates) is in the status file. Package code outside them depends on
  them: `PlainInsertRows.lean` (`generatedCells_plain`), `PlainUpdateEffect.lean`
  (`runStatement_update_ok`) and `belay/SendSuccessIfOk.lean`.
- The table-rebuild task changed `NormalizedFieldResolution`,
  `NormalizedFieldSelectResolution`, `NormalizedFieldUpdateResolution` and
  `NormalizedFieldLookups` (the `aliased` argument of the rename work) and
  adds DROP COLUMN in its part 3. Part 3 (in progress on 2026-10-27) touches
  none of the files of this task, but it changes shared laws: a field
  `dropped` in `RowLocalAtom` and `TableAtom`, new `dropColumn` constructors
  of `Syntax.Statement` and `Resolved.Statement`, the rename guard
  `Catalog.sameOutline`, and the golden text of `DbBangErrors.lean`. The
  implementation can start before part 3 is published; the branch merges part
  3 before its final `dev-build` and `test-full`.
- `Query.simple_results_append` needs a `readsBelow` width premise and
  `RowFree`; the stored-column condition reads the appended column, so it needs
  its own law.
- The surface suite takes about 1015 s of its 1200 s limit. Moved fixtures keep
  their cost; new kernel examples go to a suite with headroom (`surfaceChecks`
  takes about 570 s) or are kept small. If the surface suite would pass its
  limit, stop and report with options.
- Barrels and lakefiles (`Belay/Sqlite/Model.lean`, `Belay/Sqlite.lean`, both
  lakefiles): this task removes the old module lines and adds the new ones. S6
  automation part 3 changes `sql_run` and its step rules in parallel; this task
  does not edit them.
- The private guide is not edited here. The status file records guide changes.
- Files stay below 200 lines, with checked public docstrings, plain-words
  statements and proof sketches.
