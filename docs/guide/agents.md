# Use Belay with a coding agent

This page is for a developer who has an SQLite project and a coding agent, such
as Claude Code, Codex or Cursor. The agent writes the SQL, the claims and the
proofs. You read the claims. The page gives the review that stays with you, the
loop and three checks of the agent's work. The agent gets its instructions
from a [skill](../../skills/belay/SKILL.md) that comes with the library.

## Who does what

| Who | The work |
| --- | --- |
| The agent | Changes the SQL, states a claim for each change, runs `#sql_check`, fixes the SQL when a counterexample appears, and writes the proofs. |
| Lean's kernel | Checks each proof against the claim as written, on every build. It does not trust the agent, the search or the tactics. |
| You | Read each claim, and decide whether it says what you mean. |

## Review the claim, not the proof

A proof certifies the claim as written. When the claim says less than you
mean, the proof still passes. So you do not read proofs: a wrong proof does
not build. You read claims. The claim of the [session](#a-short-session) is
that the migration `addEmailLower` keeps the result of the read
`namedCustomers` on every database of the schema `shop`:

```lean
addEmailLower preserves namedCustomers on shop
```

Such a claim can be weaker than it looks in four ways:

1. **The premise is not your schema.** `on shop` limits the claim
   to the databases that have the tables, indexes, views and triggers of
   `shop`, with any rows. The claim says nothing about production when `shop`
   is an old copy of the schema. Keep a theorem that ties `shop` to the schema
   file, as [Set up the project](#set-up-the-project) shows.
2. **A guard excludes the databases that matter.** The claim
   `addEmailLower preserves allCustomers where noCustomers`, with the guard
   `SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM customers)`, covers only the
   databases that have no customers. Read each guard and each premise as a
   list of the databases that the claim leaves out.
3. **The claim requires nothing where the migration fails.** A migration that
   fails on every database of your schema keeps every read. Ask for the
   second claim: `Succeeds addEmailLower (·.HasCatalog shop)`.
4. **The claim compares the result of one read, and no more.** It does not
   compare the final state of the database, and it says nothing about the
   reads that it does not name.

`#explain` prints a claim in plain words, so that you can review it without
reading Lean:

```lean
#explain addEmailLower preserves namedCustomers on shop
```

```text
Claim: addEmailLower preserves namedCustomers on shop

For every valid bundled database admitted by the claim's predicate, and every
complete fresh environment, compare only when the migration succeeds at that
original context […] If the migration fails there, that instance is vacuous;
prove migration success separately. […]
Compare the original read-only query with the replacement read-only query
after the migration. […]
```

## Set up the project

Give the agent this instruction:

```text
Set up Belay in this project. Follow
https://github.com/vihren-dev/belay/blob/main/skills/belay/SKILL.md
```

The skill is a file of instructions with templates. The agent adds Belay to a
Lake project, writes the schema as a Lean file, and adds a short section to
the `AGENTS.md` or `CLAUDE.md` of the project. The rest of this section shows
what the agent makes, so that you can review it.

The lakefile makes the library of the claims a default target, so that
`lake build` compiles it, and tells Lake about the SQL files, so that a change
of a file rebuilds the claims that read it:

```toml
# lakefile.toml
name = "shop"
defaultTargets = ["Claims"]

# Here: the [[require]] block of the README's Install section.

[[input_dir]]
name = "sqlFiles"
path = "db"
text = true
filter.extension = ["sql"]

[[lean_lib]]
name = "Claims"
needs = ["sqlFiles"]
```

The lakefile is in the directory of the SQL files or above it. `Claims.lean`
imports each file of `Claims/`. One file holds the schema, and each migration
has a file of claims, such as `Claims/EmailLower.lean` for
`db/migrations/0003_email_lower.sql`.

```lean
-- Claims/Schema.lean
import Belay
open Belay.Sqlite

def shop : Database := (Database.empty.run (sql_file "db/schema.sql")).db
```

`shop` is the database that the statements of `db/schema.sql` build. The search
for counterexamples reads the SQL of the file, so the schema has one copy. A
claim about a migration is about the schema before it. When the migration is
in production and you add it to `db/schema.sql`, `shop` changes too. Give the
claims of that migration their own copy of the old schema, or delete them.

The section in `AGENTS.md` names the directory of the SQL files, the directory
of the claims and the schema database. It tells the agent to read the skill
before each change of the SQL, and it repeats the rules that the agent must
not forget: a claim for each change, no weaker claim, and `unknown` is not
`proved`. The agent reads the skill at
`.lake/packages/belay/skills/belay/SKILL.md`, in the copy of Belay that Lake
downloads. The skill thus has the version of the library that the project
builds with.

## The loop

1. The agent changes the SQL in its file.
2. It states a claim, with the schema as the premise of the claim.
3. It runs `#sql_check` on the claim and reads the answer on the command line:
   `lake --log-level=error lean Claims/EmailLower.lean`.
4. **`false`:** the answer has the rows and a script for the `sqlite3` shell.
   The agent keeps the rows as a `db!` database. It fixes the migration, or it
   changes the read of the application and keeps the fact about the old read
   with `sql_refute (db := found)`.
5. **`unknown`:** the search found no proof and no counterexample. This is not
   evidence for the claim. The agent tries `sql_auto`, then a law of the
   library for the shape of the migration, then a proof by hand.
6. **`proved`:** the agent writes the claim as a `theorem` with the proof that
   the check printed.
7. CI runs `lake build` and `belay-sql-check`, the first two of the
   [three checks](#three-checks-of-the-agents-work).

`#sql_check` is a search. It adds no theorem, and its answer does not fail
the build. Only a `theorem` or an `example` in a file that CI builds protects
you. The option `--log-level=error` hides the warnings of Belay's own files,
which Lake prints again in each run
([#372](https://github.com/vihren-dev/belay/issues/372)).

## What an agent can finish today

| The claim | Today |
| --- | --- |
| A fact about one database, and each counterexample | Reliable: `decide +kernel` and `sql_refute`. |
| A false claim about every database of a schema | `#sql_check` finds the rows when a small database shows the failure. |
| The rows of a `SELECT`, for every database of a schema | `sql_select`, with the fact `db.HasCatalog shop` as its hint. |
| The result of an insert or a delete, for every database | `sql_run` proves a part of these. It can stop at its time limit ([#359](https://github.com/vihren-dev/belay/issues/359)). |
| A read kept by `ADD COLUMN` and an `UPDATE` that fills the column | `DerivedColumnMigration.preserves_of_check` and `preserves_of_check_forall`: one line each, with a check that the kernel evaluates on the schema. The general law `queryPreserves` takes facts that the agent proves by hand. |
| A read kept by a table rebuild | A proof by hand. The rebuild of the README needs about 465 lines; they start in [`RebuildKeeps.lean`](../../tests/surface/Schema/Tests/RebuildKeeps.lean). |
| `Succeeds` for every database of a schema | For `ADD COLUMN` and an `UPDATE` that fills the column, `DerivedColumnMigration.succeeds_of_check`: one line. Else a proof by hand, such as [`RebuildSucceeds.lean`](../../tests/surface/Schema/Tests/RebuildSucceeds.lean). |

Two rules make the answers useful. Write the claim out in `#sql_check`; the
name of a definition that holds the claim gives `unknown`
([#358](https://github.com/vihren-dev/belay/issues/358)). State the schema in
the claim with `on shop`. The form without it,
`addEmailLower preserves namedCustomers`, covers every database, and
`with (schema := shop)` after it only tells the search where to look. That
claim is false: on a database where `customers` has a trigger that deletes the
rows after an update, the migration empties the table. No proof of it exists,
so its answer stays `unknown`.

## Three checks of the agent's work

```sh
lake build
lake --log-level=error exe belay-sql-check
```

```text
library Claims: 1 modules, 2 SQL sources, 0 stale
```

1. **The build passes.** Each theorem of the project has a proof that the
   kernel accepts.
2. **The SQL is the SQL of the build.** `belay-sql-check` compares the SQL
   files that the compiled claims read with the files on disk, and exits with 1
   when a file changed after the build.
3. **No proof has a hole.** A proof with `sorry` gives only a warning,
   `` declaration uses `sorry` ``. The skill tells the agent to end each
   file with `#print axioms` for its theorems, and the command of step 3 of
   the loop prints the lines:

```text
'star_read_changes' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These three axioms are the logic of Lean. `sorryAx` in the list is a hole,
and each other name is an assumption that the agent added. Then read the
report of the agent: each claim that it reports as `unknown` has no theorem.

## A short session

You ask the agent to add a column with the lowercase email to `customers`. The
application reads the table with `SELECT * FROM customers`. The agent writes
the migration and a claim:

```sql
-- db/migrations/0003_email_lower.sql
ALTER TABLE customers ADD COLUMN email_lower TEXT;
UPDATE customers SET email_lower = lower(email);
```

```lean
-- Claims/EmailLower.lean
import Claims.Schema
open Belay.Sqlite

def addEmailLower : Script := sql_file "db/migrations/0003_email_lower.sql"
def allCustomers : Script := sql r"SELECT * FROM customers"

#sql_check addEmailLower preserves allCustomers on shop
```

```text
SQL check: false.
Database:
customers:
  id | name | email
  1  | NULL | ''
sessions:
  id | customer_id | expires_at
  (no rows)
…
First program: returns a value; outputs [rows [[1, null, ""]]].
Second program: returns a value; outputs [done 0, done 1, rows [[1, null, "", ""]]].
…
```

Belay wrote one customer. After the migration, the read returns one cell more
for each row, and code that reads the cells by position can break. The
migration is right, so the agent changes the read of the application to name
its columns, keeps the fact about the old read, and checks the new read:

```lean
def namedCustomers : Script := sql r"SELECT id, name, email FROM customers"

#sql_check addEmailLower preserves namedCustomers on shop
-- SQL check: unknown; no proof or replayable counterexample was found within the budget.

def found : Database := db! r"
CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
CREATE TABLE sessions (id INTEGER PRIMARY KEY,
  customer_id INTEGER NOT NULL REFERENCES customers(id) ON DELETE CASCADE,
  expires_at INTEGER NOT NULL);
INSERT INTO customers VALUES (1, NULL, '');"

theorem star_read_changes :
    ¬ (addEmailLower preserves allCustomers on shop) := by
  sql_refute (db := found)

theorem named_read_kept_on_found :
    (found.run namedCustomers).outputs =
      ((found.run addEmailLower).db.run namedCustomers).outputs := by
  decide +kernel
```

`unknown` is not the end. `sql_auto` does not close this claim, but the
migration has the shape of a law of the library: `ADD COLUMN`, then an
`UPDATE` that fills the column from the other columns. Each law takes a check
that the kernel evaluates on the catalog of `shop`, so each proof is one line:

```lean
theorem named_read_preserved :
    addEmailLower preserves namedCustomers on shop :=
  DerivedColumnMigration.preserves_of_check (by decide +kernel)

theorem email_lower_succeeds :
    Succeeds addEmailLower (·.HasCatalog shop) :=
  DerivedColumnMigration.succeeds_of_check (by decide +kernel)
```

The checks cover a column without constraints, a value that reads only the
old columns of the row, and a read of one table that names old columns. When
a check is false, `decide` fails, and the claim stays `unknown`. The complete
example is
[`DerivedColumnOnSchema.lean`](../../tests/surface/Schema/Tests/DerivedColumnOnSchema.lean),
with the schema and the migration as SQL files; CI compiles it in a project
that requires only the `belay` package, and the skill sends the agent to it.
The agent reports three things, and each is yours to review:

- The claim about `allCustomers` is `false`, with the theorem
  `star_read_changes`. The agent changed the read of the application to named
  columns. That is a change of your code and of the claim.
- The claim about `namedCustomers` is `proved`, with the theorem
  `named_read_preserved`. Its premise is the schema `shop`.
- `Succeeds addEmailLower (·.HasCatalog shop)` is `proved`, with the theorem
  `email_lower_succeeds`. Together with `named_read_preserved`, it says that
  the migration runs on every database of `shop` and keeps the read.

## Where to go next

- The [README](../../README.md) has the table rebuild that loses rows, from the
  counterexample to the theorem.
- The [surface library](../../packages/belay/README.md) describes the notation,
  SQL in separate files, the tactics and the options of the check.
- The examples under [`tests/surface`](../../tests/surface) are proofs that CI
  compiles. An agent can read them as patterns. The migration examples are in
  [`tests/surface/Schema/Tests`](../../tests/surface/Schema/Tests).
