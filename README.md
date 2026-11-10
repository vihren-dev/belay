# Belay

Belay is a Lean library to prove facts about SQLite databases, statements and
migrations. You write SQL, state what must hold, and Lean checks it:
with a search that finds the rows that break a claim, or with a proof that
Lean's kernel verifies.

## An Exammple

Here's an example of a migration that can lose data. It's taken from ([here](https://kyrylo.org/software/2025/09/27/a-mere-add-foreign-key-can-wipe-out-your-whole-rails-sqlite-production-table.html)). We want to convert a table to a strict table.

Suppose we have a database with the following schema:

```lean
import Belay
open Belay.Sqlite

def shop : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
  CREATE TABLE sessions (id INTEGER PRIMARY KEY,
    customer_id INTEGER NOT NULL REFERENCES customers(id) ON DELETE CASCADE,
    expires_at INTEGER NOT NULL);"

```

We wwite the following migration to convert `customers` to a STRICT table. This cannot be done in-place so we recreate the table and drop the old one.


```lean
def makeStrictWrongEnforced : Script := sql r"
  PRAGMA foreign_keys = ON;
  BEGIN;
  PRAGMA foreign_keys = OFF;
  CREATE TABLE customers_new (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL) STRICT;
  INSERT INTO customers_new SELECT id, name, email FROM customers;
  DROP TABLE customers;
  ALTER TABLE customers_new RENAME TO customers;
  COMMIT;"
```

There is a mistake which is difficult to spot: PRAGMA doesn't work in a transaction. So when we run `DROP TABLE customers`, all rows in the table `sessions` will also be deleted due to the `ON DELETE CASCADE` clause. 

### The counterexample

The migration will be correct if it preserves the behaviour of the following query

```lean
def allSessions : Script := sql r"SELECT id, customer_id, expires_at FROM sessions"
```

The following statement will try to prove it or find a counterexample:

```lean
#sql_check makeStrictWrongEnforced preserves allSessions with (schema := shop)
```

The output would show:
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
block. Paste the replay script into the `sqlite3` shell and watch native SQLite
do the same.

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
kernel ran SQLite's semantics and certified both, and does so again on every
build.

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

The following claims that for **every database** with the given `shop` schema, the behaviour of the `allSessions` query will be preserved after the correct migration.

```lean
theorem makeStrict_preserves_allSessions :
    Migration.QueryPreserves (send makeStrict) allSessions (·.HasCatalog shop)
```

This is a claim which your coding agent can prove and the Lean proof checker can verify. You can see one proof in [`RebuildKeeps.lean`](tests/surface/RebuildKeeps.lean).

## Try it on your schema

Put your `CREATE TABLE` statements in `db!`, your migration in `sql`, and state
`preserves` for the reads you care about. `#sql_check` answers `false` with the
rows and a replay script, `proved`, or `unknown`. A counterexample becomes a
test with `sql_refute (db := found)`.

## What you can state

| Level | The question | Notation | Who settles it |
| --- | --- | --- | --- |
| 1 | Is the SQL valid against this schema? | `sql!`, `db!` | The elaborator, when the file compiles |
| 2 | Does it run without an error? | `succeeds`, `succeeds where` | `#sql_check` and tactics, or a proof |
| 3 | What does it do to the data? | `ensures`, `≈`, `preserves` | `#sql_check` and tactics, or a proof |
| 4 | Does the whole application behave the same? | `simulates` | A proof that you or an agent write |

You can stop at the level you need.

## Why trust it

We currently model a part of SQLite 3.51.0 semantics which are checked
against SQLite's own test suite and the project's corpora: 5,525 cases,
replayed against native SQLite and against the model, with no disagreement
allowed. SQL outside the model is refused. A proof is about the statements, not about locks, query plans or concurrency; the [execution profile](docs/execution-profile.md) states the connection
settings it assumes.

## Supported SQL

Tables with constraints, generated columns, `STRICT` and `WITHOUT ROWID`;
indexes, views and triggers; `ALTER TABLE`; transactions; `INSERT`, `UPDATE`
and `DELETE` with `RETURNING` and upserts; `SELECT` with joins, grouping,
ordering, limits, subqueries, common table expressions and compound queries;
the foreign-key and recursive-trigger pragmas. The exact list is in the
[supported subset](docs/semantic-subset.md).

## Install

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
counterexample appears, and writes the proofs. The kernel checks the proof;
you review the claim, and `#explain` prints a claim in plain words.

## Documentation

- The [surface library](packages/belay/README.md): programs and runs, SQL in
  separate files, claims and the check.
- The [supported subset](docs/semantic-subset.md) and the
  [execution profile](docs/execution-profile.md).
- The [checked Lean API reference](docs/api-reference.md) of the model.
- The examples under [`tests/surface`](tests/surface), which CI compiles.

## Community and support

Ask questions in [Discussions](https://github.com/vihren-dev/belay/discussions).
Report a case where the model and native SQLite disagree in
[Issues](https://github.com/vihren-dev/belay/issues), with the SQL, the output
of the `sqlite3` shell and the block that Belay printed. To build and change
the repository, read [CONTRIBUTING.md](CONTRIBUTING.md).

## License

Project code is MIT licensed. SQLite is upstream public-domain software. Lean
and Nix dependencies retain their respective upstream licenses.
