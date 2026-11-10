# Belay

Belay is a Lean library to prove facts about SQLite databases, statements and
migrations. You write SQL as SQL, state what must hold, and Lean checks it:
with a search that finds the rows that break a claim, or with a proof that
Lean's kernel verifies.

## A migration that passes its tests and loses data

The task: make `customers` a STRICT table, so that SQLite refuses a value of the
wrong type. No version of SQLite can do that in place. The migration copies the
table, drops the old one and renames the copy, as the recipe on sqlite.org says.
The migration below follows the recipe and has a bug that deletes the rows of
another table. The same bug hit a Rails application when `add_foreign_key`
rebuilt a table and SQLite deleted every row of a child table
([write-up](https://kyrylo.org/software/2025/09/27/a-mere-add-foreign-key-can-wipe-out-your-whole-rails-sqlite-production-table.html)).

```lean
import Belay
open Belay.Sqlite

def shop : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
  CREATE TABLE sessions (id INTEGER PRIMARY KEY,
    customer_id INTEGER NOT NULL REFERENCES customers(id) ON DELETE CASCADE,
    expires_at INTEGER NOT NULL);"

def makeStrictWrongEnforced : Script := sql r"
  PRAGMA foreign_keys = ON;
  BEGIN;
  PRAGMA foreign_keys = OFF;
  CREATE TABLE customers_new (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL) STRICT;
  INSERT INTO customers_new SELECT id, name, email FROM customers;
  DROP TABLE customers;
  ALTER TABLE customers_new RENAME TO customers;
  COMMIT;"

def allSessions : Script := sql r"SELECT id, customer_id, expires_at FROM sessions"
```

SQL is SQL, in raw strings, and `db!` runs the schema when the file compiles.
The schema has no rows: you do not know which data breaks the migration.

### The counterexample

State what must stay true, and let Belay find the rows:

```lean
#sql_check makeStrictWrongEnforced preserves allSessions with (schema := shop)
```

```text
SQL check: false.
Database:
customers:
  id | name | email
  1  | NULL | ''
sessions:
  id | customer_id | expires_at
  1  | 1           | 0
allSessions: rows [[1, 1, 0]]
makeStrictWrongEnforced, statement 1: done 0
makeStrictWrongEnforced, statement 2: done 0
makeStrictWrongEnforced, statement 3: done 0
makeStrictWrongEnforced, statement 4: done 0
makeStrictWrongEnforced, statement 5: done 1
makeStrictWrongEnforced, statement 6: done 0
makeStrictWrongEnforced, statement 7: done 0
makeStrictWrongEnforced, statement 8: done 0
Construction:
CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
…
SQLite replay:
.bail off
CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
…
```

Belay wrote one customer and one session, the smallest database of the schema
that breaks the claim, and every statement of the migration reported success.
Two rules of SQLite cause it: a pragma inside a transaction does nothing, so
foreign keys stay on; and `DROP TABLE` with foreign keys on deletes the parent
rows one by one, which cascades into `sessions`. The editor prints the whole
block, with the SQL that builds the database and a script for the `sqlite3`
shell that replays the answer on native SQLite. The search fills only the
tables that the claim touches, respects NOT NULL, keys and foreign keys, and
has refuted a claim on a schema of real size: six tables, triggers, CHECK
constraints and foreign keys
([`CheckConsumerSize.lean`](tests/surface/CheckConsumerSize.lean)). The check
above answers in about nine seconds on the development machine, after the
import.

### The fact, in the kernel

Keep the rows that Belay found, and state the fact as a theorem of the file:

```lean
def found : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
  CREATE TABLE sessions (id INTEGER PRIMARY KEY,
    customer_id INTEGER NOT NULL REFERENCES customers(id) ON DELETE CASCADE,
    expires_at INTEGER NOT NULL);
  INSERT INTO customers VALUES (1, NULL, '');
  INSERT INTO sessions VALUES (1, 1, 0);"

example : (found.run makeStrictWrongEnforced).outputs.allOk = true ∧
    ((found.run makeStrictWrongEnforced).db.run allSessions).outputs.getLast? = some (.rows []) := by
  decide +kernel
```

Every statement of the migration succeeds, and the session is gone. Lean's
kernel ran SQLite's semantics and certified both, in about one second, and does
so again on every build.

### The fix and the proof

```lean
def makeStrict : Script := sql r"
  PRAGMA foreign_keys = OFF;           -- before the transaction, where it takes effect
  BEGIN;
  CREATE TABLE customers_new (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL) STRICT;
  INSERT INTO customers_new SELECT id, name, email FROM customers;
  DROP TABLE customers;
  ALTER TABLE customers_new RENAME TO customers;
  PRAGMA foreign_key_check;            -- fails the migration on a dangling reference
  COMMIT;
  PRAGMA foreign_keys = ON;"           -- on again after the commit

example : (found.run makeStrict).outputs.allOk = true ∧
    ((found.run makeStrict).db.run allSessions).outputs.getLast? = some (.rows [[1, 1, 0]]) := by
  decide +kernel
```

A fact about one database is one line. A fact about every database of the
schema is a theorem:

```lean
theorem makeStrict_preserves_allSessions :
    Migration.QueryPreserves (send makeStrict) allSessions (·.HasCatalog shop)
```

Where the fixed migration succeeds, the sessions read the same before and after
it, on every database with the schema `shop` and with any rows. The
repository proves it in [`RebuildKeeps.lean`](tests/surface/RebuildKeeps.lean),
in about 470 lines over four files, and Lean's kernel checks the proof on every
build.

## What you can state

| Level | The question | Notation | Who settles it |
| --- | --- | --- | --- |
| 1 | Is the SQL valid against this schema? | `sql!`, `db!` | The elaborator, when the file compiles |
| 2 | Does it run without an error? | `succeeds`, `succeeds where` | `#sql_check` and tactics, or a proof |
| 3 | What does it do to the data? | `ensures`, `≈`, `preserves` | `#sql_check` and tactics, or a proof |
| 4 | Does the whole application behave the same? | `simulates` | A proof that you or an agent write |

You can stop at the level you need. `#sql_check` answers `proved`, `false` with
a replayable counterexample, or `unknown`; `unknown` is not evidence.

## What a proof means

- The model follows SQLite 3.51.0 under a stated
  [execution profile](docs/execution-profile.md): foreign keys and recursive
  triggers off on a new connection, the documented limits.
- The model is checked against SQLite's own test suite and the project's
  corpora: 5,525 cases, replayed against native SQLite and against the model,
  with no disagreement allowed. Unsupported SQL is refused with a reason, never
  approximated.
- A proved claim holds for SQLite 3.51.0 if the model is faithful. The
  conformance evidence is how you can check that condition yourself.
- A proof covers the semantics of the statements. It does not cover locks,
  query plans, concurrency, durability, extensions, or which database file a
  statement reaches.

## Supported SQL

Tables with constraints, generated columns, `STRICT` and `WITHOUT ROWID`;
indexes, views and triggers; `ALTER TABLE`; transactions; `INSERT`, `UPDATE`
and `DELETE` with `RETURNING` and upserts; `SELECT` with joins, grouping,
ordering, limits, subqueries, common table expressions and compound queries;
the foreign-key and recursive-trigger pragmas. The rest is refused at its byte
range when the file compiles, or ends a run as `Output.unmodeled`; neither is
ever a wrong answer. The exact list is in the
[supported subset](docs/semantic-subset.md).

## Install and try

Install [elan](https://github.com/leanprover/elan), then add Belay to a Lake
project:

```toml
# lakefile.toml
name = "myproject"
defaultTargets = ["MyProject"]

[[require]]
name = "belay"
git = "https://github.com/vihren-dev/belay"
rev = "main"
subDir = "packages/belay"

[[lean_lib]]
name = "MyProject"
```

```sh
lake update
lake build
```

The first build compiles the model and SQLite's parser once; later builds
reuse them. Then put the blocks above in a file of your project and open it in
an editor with the Lean language server. The surface library's
[README](packages/belay/README.md) describes the notation, SQL in separate
files, and the options of the check.

## With a coding agent

An agent writes SQL, states claims, runs `#sql_check`, fixes the SQL when a
counterexample appears, and writes the proofs. The kernel accepts or rejects
every proof and cannot be argued with. The kernel checks the proof, not the
claim: you review the claim, and `#explain` prints a claim in plain words. A
proof of a weak claim is still a proof, so read the guards and the schema
premise. A counterexample stays in the file as a `sql_refute` test.

## Documentation

- The [surface library](packages/belay/README.md): programs and runs, SQL in
  separate files, claims and the check.
- The [supported subset](docs/semantic-subset.md) and the
  [execution profile](docs/execution-profile.md).
- The [checked Lean API reference](docs/api-reference.md) of the model.
- The examples under [`tests/surface`](tests/surface), which CI compiles.
- The design records under [`docs`](docs), `adr-NNNN-*.md`, for the reasons
  behind the library.

## Community and support

Ask questions in [Discussions](https://github.com/vihren-dev/belay/discussions).
Report a case where the model and native SQLite disagree in
[Issues](https://github.com/vihren-dev/belay/issues); it is the most valuable
report you can send. Include the SQL, the output of the `sqlite3` shell with
its version, and the block that Belay printed.

## Repository layout

The model is `packages/belay-sqlite-model`, the parser `packages/belay-sqlite-text`,
and the surface that you import `packages/belay`. The conformance evidence is
under `conformance/` and `judge/`. [CONTRIBUTING.md](CONTRIBUTING.md) explains
how to build and test the repository.

## License

Project code is MIT licensed. SQLite is upstream public-domain software. Lean
and Nix dependencies retain their respective upstream licenses.
