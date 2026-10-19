# Schema features in the out-of-scope corpus cases

Question: which schema features (constraints, table options, index forms) keep corpus
cases out of the model's scope, and which of them would bring the most cases into scope
when the model supports them? This is the measurement behind
[ADR 0014](../../docs/adr-0014-schema-features.md).

Measured on 2026-10-19 against the verdict of the ADR 0013 stack tip (#169), which has
4,992 out-of-scope cases over all corpora. Corpus v5 is the newest and largest upstream
corpus (4,376 cases, 3,398 out of scope), and the older upstream corpora overlap with it,
so this README reports corpus v5 and lists the others at the end.

## How to reproduce

```sh
nix-build integrity/judge.nix -A verdict --no-out-link   # prints the verdict directory
python3 experiments/schema-features/measure.py VERDICT/report.json conformance/corpus-v5
```

`measure.py` takes several corpus directories and prints JSON for each one.

## Method

- **Cases.** Only cases with the verdict `MODEL_UNSUPPORTED`.
- **Scan.** The scan is lexical, over `setupSql` and `migrationSql`. A tokenizer drops
  strings, blobs, quoted names and comments. Statements split at semicolons, except in
  a trigger body.
- **Schema features.** These come from each `CREATE TABLE`, each `CREATE INDEX` and each
  `ALTER TABLE ... ADD COLUMN`. Two features describe a CREATE that runs in the script
  rather than one that describes the starting schema, and the SQL alone does not show
  that. The scan takes those two from the model's reason (`create-index-runs` and
  `create-table-runs-with-constraints`).
- **Other features.** These are lexical marks of features outside this ADR: triggers,
  views, `DROP`, `PRAGMA`, `ALTER TABLE ... RENAME` or `DROP COLUMN`, `WITH`,
  subqueries, compound selects, window functions, `INSERT ... SELECT`, and other
  commands.
- **Column meanings** in the table below:
  - *Uses*: the out-of-scope cases that use the feature.
  - *Refused for it*: those that the model refuses for a schema reason, which is the
    first restriction the model meets.
  - *Clean*: those with no other feature.
  - *Only feature*: clean cases in which this is the only schema feature.

A clean case is the best estimate of a case that support for its schema features brings
into scope. A restriction that the scan does not see, such as an unmodeled function, can
still stop it, so the clean counts are upper bounds.

## Results (corpus v5)

Of the 3,398 out-of-scope cases, 1,529 use at least one schema feature and 532 of those
are clean.

| Feature | Uses | Refused for it | Clean | Only feature |
|---|---|---|---|---|
| `foreign-key` (`REFERENCES`, `FOREIGN KEY`) | 349 | 21 | 15 | 14 |
| `collate` (column, key or index term) | 330 | 322 | 87 | 43 |
| `without-rowid` | 277 | 255 | 163 | 120 |
| `partial-index` (`CREATE INDEX ... WHERE`) | 252 | 250 | 138 | 120 |
| `expression-index` (a key term that is not a column) | 150 | 148 | 53 | 22 |
| `create-table-as-select` | 106 | 0 | 1 | 1 |
| `check` | 92 | 91 | 47 | 35 |
| `generated-column` | 78 | 78 | 30 | 17 |
| `create-index-runs` (an index built over existing rows) | 39 | 39 | 33 | 33 |
| `create-table-runs-with-constraints` | 32 | 32 | 25 | 25 |
| `index-sort-order` (`ASC` or `DESC` in a key) | 16 | 15 | 10 | 8 |
| `named-constraint` (`CONSTRAINT name ...`) | 14 | 14 | 8 | 8 |
| `default-expression` (`DEFAULT (expr)`) | 9 | 8 | 2 | 2 |
| `autoincrement` | 7 | 0 | 2 | 2 |
| `strict` | 4 | 4 | 4 | 4 |

The model meets another restriction first in nearly all foreign-key cases: their profile
enforces foreign keys, which the model refuses. In `create-table-as-select` cases it meets
the `SELECT` first.

**Order of the most clean cases.** At each step, the feature that brings in the most clean
cases whose schema features are all supported by then (cumulative):

| Step | Feature | Clean cases |
|---|---|---|
| 1 | `partial-index` | 120 |
| 2 | `without-rowid` | 252 |
| 3 | `collate` | 307 |
| 4 | `expression-index` | 358 |
| 5 | `check` | 402 |
| 6 | `create-index-runs` | 435 |
| 7 | `generated-column` | 465 |
| 8 | `create-table-runs-with-constraints` | 490 |
| 9 | `foreign-key` (inert, without enforcement) | 505 |
| 10 | the other seven | 532 |

**What else stops the schema-feature cases.** 997 of the 1,529 cases also use another
feature. Some use only one other feature:

| Other feature | Cases |
|---|---|
| `PRAGMA` | 273 |
| `DROP` | 110 |
| `ALTER TABLE` RENAME or DROP COLUMN | 76 |
| compound select | 29 |
| subquery | 27 |
| `INSERT ... SELECT` | 26 |
| other commands | 21 |
| trigger | 10 |
| view | 4 |

- **PRAGMA.** In those 273 cases the pragmas are `foreign_keys=` (248) and
  `foreign_key_check` (207); they belong with foreign-key enforcement.
- **DROP.** The DROP cases use `DROP INDEX` (75) and `DROP TABLE` (38).

## Other corpora

| Corpus | Out of scope | With a schema feature | Clean |
|---|---|---|---|
| v1 | 164 | 74 | 23 |
| v2 | 164 | 74 | 23 |
| v3 | 306 | 130 | 51 |
| v4 | 955 | 331 | 124 |
| v6 | 3 | 3 | 3 |

The authored corpora v7 to v28 have no out-of-scope case with a schema feature. In v1 to
v4 the first features of the order are `check`, `strict`, `generated-column`,
`create-index-runs` and `create-table-runs-with-constraints`.

## Native behaviour checked for the ADR

Checked with the pinned SQLite 3.51.0 shell, one statement per line:

- **CHECK.** A failing CHECK reports `CHECK constraint failed: a>0`, with the expression
  text as written, or the name of a named constraint (`bpos`). A NULL result passes.
- **Partial unique index.** It constrains only the rows that satisfy its `WHERE` clause.
- **`WITHOUT ROWID`.**
  - A full scan returns the rows in primary-key order.
  - The primary key is NOT NULL.
  - `rowid` is a prepare error: `no such column: rowid`.
- **`COLLATE NOCASE`.** On a column it applies to UNIQUE (`'A'` and `'a'` conflict) and to
  `x = 'A'`.
- **STRICT.**
  - The value is converted first: `'12'` becomes the INTEGER 12.
  - A value that stays TEXT fails with `cannot store TEXT value in INTEGER column s.a`.
- **Generated columns.**
  - `INSERT` into one is a prepare error: `cannot INSERT into generated column "b"`.
  - `VIRTUAL` and `STORED` read the same values.
- **`CREATE UNIQUE INDEX` over duplicate rows.**
  - Over a column key it fails with `UNIQUE constraint failed: e.a`.
  - Over an expression key it fails with `UNIQUE constraint failed: index 'ex'`.
