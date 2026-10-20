# `DROP INDEX` and `DROP TABLE` (ADR 0014, slice 7)

Created 2026-10-20. Status: DONE (pull requests #191 and #192).
Status file: [status](20261020-drop-index-table.status.md).
Specification: [ADR 0014](../docs/adr-0014-schema-features.md), D7.

## Pull requests

- **A (subject):** the model, the frontend and an authored corpus, stacked on slice 6
  (PR B of slice 6). Nothing under `judge/` changes.
- **B (claims), only if cases newly agree.**

## Outcome

1. **Syntax.** `DROP INDEX [IF EXISTS] name` and `DROP TABLE [IF EXISTS] name` map to the
   Syntax IR. A schema name stays a frontend refusal, as for the other statements.
2. **Prepare errors**, checked natively with 3.51.0, with the name compared as SQLite
   compares names (ASCII case ignored):
   - `no such table: x` for a name that is no table, also for the name of an index;
   - `no such index: x` for a name that is no index, also for the name of a table;
   - `IF EXISTS` turns those two into a statement that does nothing;
   - `table sqlite_master may not be dropped` for `sqlite_master` and `sqlite_schema`,
     also with `IF EXISTS`;
   - `index associated with UNIQUE or PRIMARY KEY constraint cannot be dropped` for an
     index of a constraint (`sqlite_autoindex_t_1`). The catalog does not name those
     indexes, so a DROP INDEX of a name that begins with `sqlite_autoindex_` and that is no
     catalog index is a model restriction.
3. **Execution.** `DROP INDEX` removes the index from the catalog. `DROP TABLE` removes the
   table, its rows and its indexes. Later catalog objects move to lower positions, and the
   indexes of other tables keep their tables. The catalog function of each DROP is shared by
   resolution and execution (ADR 0013), so statements after a DROP resolve against the
   catalog that execution has. A DROP in a transaction that is rolled back comes back with
   its rows.
4. **Scope.** The model has no triggers, views or enforced foreign keys, so a DROP that
   would affect one of them is out of scope as before; the profiles keep `foreign_keys`
   off.
5. **Laws.** The laws that hold for every statement hold for the two DROP statements too:
   unique folded names (`resolve_namesUnique`), the agreement of the resolver's and the
   execution's catalog (`advance_agrees`, `runSqlFrom_agrees`) and the resolve-state fold
   (`resolveFrom_after`). The extension law `step_extends`, whose statement says that no
   table is lost, cannot hold for DROP and excludes it. (Amended 2026-10-20: conformance to
   the catalog has lemmas per statement, not a law for every statement, so it is not listed.)

## Tests

- Lean examples: each prepare error and `IF EXISTS`; a DROP INDEX and a DROP TABLE followed
  by statements on later objects; an index of a later table that keeps its table; a DROP
  rolled back in a transaction; a CREATE after a DROP of the same name.
- An authored corpus (`conformance/authored_drops.py`) of these cases, each with a kernel
  proof, recorded as a new corpus.
- The verdict of every corpus: cases that newly agree and none that leave AGREE.
- Mutants: a DROP TABLE that keeps the table's indexes, a DROP that does not move the later
  positions, and `IF EXISTS` that still reports `no such table`, each killed by an authored
  case.

## Key points

- **Positions.** `Database.rows` and `Catalog` are parallel lists by position, and
  `CatalogIndex.table` is a catalog position. A removal must shift each later index's table
  position. Today the catalog only grows (`Catalog.createTable`, `Catalog.createIndex`,
  `Catalog.addColumn`), and laws such as `Conforms.createTable` and `advance_agrees` are
  built on that; the new removal functions need their own lemmas.
- **Restrictions.** `conformance/requirement_cases.py` has a `drop-index` case; check what
  it expects today. The restriction registry and `docs/semantic-subset.md` list the new
  restriction.
- **Harness.** `PRAGMA` rows and the visible schema come from the catalog
  (`conformance/predict_render.py`); a removed table must leave no rows there. Check the
  `changes` value that the recorder reports for a DROP.
