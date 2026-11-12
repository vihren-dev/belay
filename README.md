# Belay

Belay is a Lean library to prove facts about SQLite databases, statements and
migrations. You write SQL, state what must hold, and Lean checks it:
with a search that finds the rows that break a claim, or with a proof that
Lean's kernel verifies.

## An example

This example is a migration that can lose data. The same mistake deleted a
table of a Rails application
([write-up](https://kyrylo.org/software/2025/09/27/a-mere-add-foreign-key-can-wipe-out-your-whole-rails-sqlite-production-table.html)).
The task is to make a table a STRICT table.

The database has this schema. It has no rows: you do not know which data
breaks a migration.

```lean
import Belay
open Belay.Sqlite

def shop : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
  CREATE TABLE sessions (id INTEGER PRIMARY KEY,
    customer_id INTEGER NOT NULL REFERENCES customers(id) ON DELETE CASCADE,
    expires_at INTEGER NOT NULL);"
```

This migration makes `customers` a STRICT table. SQLite cannot do that in
place, so the migration copies the table, drops the old one and renames the
copy.

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

The migration has a mistake that is difficult to see: `PRAGMA foreign_keys`
does nothing inside a transaction, so foreign keys stay on. `DROP TABLE
customers` then deletes the customers row by row, and `ON DELETE CASCADE`
deletes the sessions of each customer.

### The counterexample

A correct migration must keep the result of this query:

```lean
def allSessions : Script := sql r"SELECT id, customer_id, expires_at FROM sessions"
```

This command tries to prove that claim or to find a counterexample:

```lean
#sql_check makeStrictWrongEnforced preserves allSessions with (schema := shop)
```

The output is:

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
The editor prints the whole block. Paste the replay script into the `sqlite3`
shell and watch native SQLite do the same.

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

This theorem claims that on **every database** with the schema `shop`, the
query `allSessions` gives the same result after the fixed migration:

```lean
theorem makeStrict_preserves_allSessions :
    makeStrict preserves allSessions on shop
```

Your coding agent can prove such a claim, and Lean's kernel checks the proof.
One proof is in [`RebuildKeeps.lean`](tests/surface/Schema/Tests/RebuildKeeps.lean).

## Try it on your schema

Put your `CREATE TABLE` statements in `db!`, your migration in `sql`, and state
`migration preserves read on schema` for the reads you care about. Without
`on schema`, the claim is about every database, also one with other tables and
triggers. `#sql_check` answers `false` with the
rows and a replay script, `proved`, or `unknown`. A counterexample becomes a
test with `sql_refute (db := found)`.

## What you can state

| The question | Notation | Who settles it |
| --- | --- | --- |
| Is the SQL valid against this schema? | `sql!`, `db!` | The elaborator, when the file compiles |
| Does it run without an error? | `succeeds`, `succeeds where` | `#sql_check` and tactics, or a proof |
| What does it do to the data? | `ensures`, `≈`, `preserves`, `preserves … on` | `#sql_check` and tactics, or a proof |
| Does the whole application behave the same? | `simulates` | A proof that you or an agent write |

The questions are independent. A migration that fails keeps every read, so
state `succeeds` together with `preserves`.

A fact about one run on one database, such as the two examples with
`found.run` above, is settled by Lean's kernel, which runs the statements. A
claim in the notation of the table is about every database. For such a claim,
`#sql_check` searches for a counterexample and tries the library's proofs, and
a proof by you or an agent settles the rest.

## Why trust it

Belay models a part of SQLite 3.51.0. The model is checked against SQLite's
own test suite and the project's corpora: 5,525 cases, replayed against native
SQLite and against the model, with no disagreement allowed. SQL outside the
model is refused. A proof is about the statements, not about locks, query
plans or concurrency; the [execution profile](docs/execution-profile.md)
states the connection settings it assumes.

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
[Use Belay with a coding agent](docs/guide/agents.md) has the loop, the checks
of the agent's work. To start, tell your agent to set up Belay with the
[skill](skills/belay/SKILL.md) of this repository.

## Documentation

- [Use Belay with a coding agent](docs/guide/agents.md), with
  the [skill for the agent](skills/belay/SKILL.md).
- The [surface library](packages/belay/README.md): programs and runs, SQL in
  separate files, claims and the check.
- The [supported subset](docs/semantic-subset.md) and the
  [execution profile](docs/execution-profile.md).
- The [checked Lean API reference](docs/api-reference.md) of the model.
- The examples under [`tests/surface`](tests/surface), which CI compiles. The
  migration examples are in
  [`tests/surface/Schema/Tests`](tests/surface/Schema/Tests).

## Community and support

Ask questions in [Discussions](https://github.com/vihren-dev/belay/discussions).
Report a case where the model and native SQLite disagree in
[Issues](https://github.com/vihren-dev/belay/issues), with the SQL, the output
of the `sqlite3` shell and the block that Belay printed. The project accepts
issues, reproductions of bugs and new test cases, and does not accept pull
requests that change code; [CONTRIBUTING.md](CONTRIBUTING.md) has the details
and the build instructions.

## License

Project code is MIT licensed. SQLite is upstream public-domain software. Lean
and Nix dependencies retain their respective upstream licenses.
