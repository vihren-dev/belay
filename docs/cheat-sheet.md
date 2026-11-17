# Belay cheat sheet

This page is for a developer who states claims about SQL and reviews them. A
coding agent writes the proofs, and Lean's kernel checks each proof on every
build, so the page does not show how to prove a claim. It shows how to write
a claim and how to read one. The page covers the two claims that a migration
needs: `succeeds` and `preserves`.

## The three parts of a claim

```lean
import Belay
open Belay.Sqlite

-- The schema: the database that these statements build.
def shop : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
  CREATE TABLE sessions (id INTEGER PRIMARY KEY,
    customer_id INTEGER NOT NULL REFERENCES customers(id) ON DELETE CASCADE,
    expires_at INTEGER NOT NULL);"

-- The change.
def addEmailLower : Script := sql r"
  ALTER TABLE customers ADD COLUMN email_lower TEXT;
  UPDATE customers SET email_lower = lower(email);"

-- A read of the application.
def namedCustomers : Script := sql r"SELECT id, name, email FROM customers"
```

| The part | In a Lean file | From an SQL file |
| --- | --- | --- |
| The schema | `db! r"…"` | `(Database.empty.run (sql_file "db/schema.sql")).db` |
| The change | `sql r"…"` | `sql_file "db/migrations/0003.sql"` |
| A read | `sql r"…"` | `sql_file "db/queries/customers.sql"` |

## The two claims

| The claim | The meaning |
| --- | --- |
| `M succeeds on shop` | On every database with the schema of `shop`, with any rows, `M` runs without an error. |
| `M preserves Q on shop` | On every database with the schema of `shop` on which `M` runs without an error, the read `Q` returns the same result after `M` as before `M`. |

State the two claims together. `preserves` requires nothing on a database
where the migration fails, so a migration that always fails preserves every
read.

```lean
addEmailLower succeeds on shop
addEmailLower preserves namedCustomers on shop
```

State `preserves` for each read of the application that must not change. The
claim compares the result of that one read. It does not compare the other
reads or the final state of the database.

## The scope of a claim

| You write | The claim covers |
| --- | --- |
| `M succeeds` | Every database, also one with other tables and triggers, and the database without tables. A migration that changes a table fails on the database without tables, so this claim is false for it. |
| `M succeeds on shop` | Every database with the tables, indexes, views and triggers of `shop`, with any rows. |
| `M succeeds on shop where guard` | The databases of `shop` on which the query `guard` returns a row. |
| `∀ email : Value, M preserves (byEmail email) on shop` | The claim for every value of the parameter of a read. |

The same scope words apply to `preserves`.

A guard is one read-only statement. Write a condition as
`SELECT 1 WHERE <condition>`:

```lean
def noSessions : Script := sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM sessions)"

addEmailLower preserves namedCustomers on shop where noSessions
```

A read with a parameter is a function that gives a script:

```lean
def customerByEmail (email : Value) : Script :=
  sql r"SELECT id FROM customers WHERE email = ?1" email

∀ email : Value, addEmailLower preserves (customerByEmail email) on shop
```

## Check a claim

```lean
#sql_check addEmailLower preserves allCustomers on shop
```

`#sql_check` searches for a database that breaks the claim, and it tries the
proofs of the library. It adds no theorem.

| The answer | The meaning | The next step |
| --- | --- | --- |
| `false` | The answer shows a database that breaks the claim and a script for the `sqlite3` shell. | Fix the SQL or the claim. Keep the database as a test. |
| `proved` | The library has a proof. | Write the claim as a `theorem` with the proof that the answer prints. |
| `unknown` | The search found no counterexample and no proof. This is not evidence for the claim. | The agent writes a proof. |

Expect `unknown` for a true claim. The search is for counterexamples, and
only a small database can show one. A claim is proved when it is a `theorem`
in a file that the build compiles:

```lean
theorem email_lower_succeeds : addEmailLower succeeds on shop :=
  DerivedColumnMigration.succeeds_of_check (by decide +kernel)

theorem named_read_preserved : addEmailLower preserves namedCustomers on shop :=
  DerivedColumnMigration.preserves_of_check (by decide +kernel)
```

These two proofs have one line, because the library has a law for a column
that is added and filled. Most proofs are longer. They are the work of the
agent, and you do not read them.

## A fact about one database

The kernel runs the statements on a database with rows, so such a fact needs
no proof by hand. Use it for a regression test:

```lean
def one : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
  CREATE TABLE sessions (id INTEGER PRIMARY KEY,
    customer_id INTEGER NOT NULL REFERENCES customers(id) ON DELETE CASCADE,
    expires_at INTEGER NOT NULL);
  INSERT INTO customers VALUES (1, NULL, 'A@x.io');"

-- The migration runs on this database.
example : (one.run addEmailLower).outputs.allOk = true := by decide +kernel

-- The read returns the same rows after the migration.
example : ((one.run addEmailLower).db.run namedCustomers).outputs =
    (one.run namedCustomers).outputs := by decide +kernel
```

A counterexample makes a claim false for good. `sql_refute` checks that the
database breaks the claim:

```lean
def allCustomers : Script := sql r"SELECT * FROM customers"

theorem star_read_changes : ¬ (addEmailLower preserves allCustomers on shop) := by
  sql_refute (db := one)
```

## Read a claim before you accept it

A proof certifies the claim as written. Ask these questions about each claim
that an agent gives you:

1. **Is `shop` your schema?** The claim says nothing about production when
   `shop` is an old copy. Build `shop` from the schema file with `sql_file`.
2. **Which databases does the guard leave out?** Each `where` makes the claim
   smaller. A guard that gives an error leaves the database out too.
3. **Is `succeeds` stated too?** Without it, `preserves` says nothing about a
   database on which the migration fails.
4. **Does each read that matters have its claim?** One claim covers one read.
5. **Is the claim a `theorem`?** `#sql_check` does not fail the build, and
   `unknown` is not `proved`.

`#explain` prints a claim in plain words:

```lean
#explain addEmailLower succeeds on shop
```

## Check the work of an agent

```sh
lake build
lake --log-level=error exe belay-sql-check
```

| The check | It shows |
| --- | --- |
| `lake build` exits with 0 | The kernel accepts each proof. |
| `belay-sql-check` reports `0 stale` | The claims were compiled with the SQL files that are on disk now. |
| `#print axioms name` shows only `propext`, `Classical.choice` and `Quot.sound` | The proof has no `sorry` and no assumption that the agent added. |

## What a proof is about

A proof is about Belay's model of SQLite 3.51.0. The model is tested against
SQLite, and that agreement is not proved. A proof is about the statements. It
is not about locks, query plans or concurrency.

## Read more

- [Use Belay with a coding agent](guide/agents.md): the loop, a complete
  session and what an agent can finish today.
- The [surface library](../packages/belay/README.md): the other claims
  (`translates`, `ensures`, `≈`, `commutes with`, `simulates`), SQL in
  separate files and the options of the check.
- The [supported subset](semantic-subset.md) and the
  [execution profile](execution-profile.md).
