# Belay cheat sheet

## Define a schema, a migration and a read

```lean
import Belay
open Belay.Sqlite

def shop : Database := db! r"CREATE TABLE customers (id INTEGER PRIMARY KEY, email TEXT NOT NULL);"
def M : Script := sql r"ALTER TABLE customers ADD COLUMN email_lower TEXT"
def Q : Script := sql r"SELECT id, email FROM customers"
def byEmail (email : Value) : Script := sql r"SELECT id FROM customers WHERE email = ?1" email
```

## Load them from files

```lean
def shop : Database := (Database.empty.run (sql_file "db/schema.sql")).db
def M : Script := sql_file "db/migrations/0003_email_lower.sql"
def Q : Script := sql_file "db/queries/customers.sql"
```

A path is relative to the Lake package that owns the Lean file.

## State a claim

| Claim | Meaning |
| --- | --- |
| `M succeeds on shop` | On every database with the schema of `shop`, `M` runs without an error. |
| `M preserves Q on shop` | On every such database on which `M` runs without an error, `Q` returns the same result after `M` as before. |
| `∀ email : Value, M preserves (byEmail email) on shop` | The same, for every value of the parameter. |
| `M preserves Q on shop where noCustomers` | Only for the databases on which the query `noCustomers` returns a row. |
| `M succeeds`, `M preserves Q` | For every database, with any schema. |

State `succeeds` with each `preserves`: a migration that fails preserves every
read.

## Check a claim

```lean
#sql_check M preserves Q on shop   -- false with a database, proved, or unknown
#explain M preserves Q on shop     -- the claim in plain words
theorem q_kept : M preserves Q on shop := …   -- the proof, from your agent
```

`unknown` is not evidence. A claim is proved when it is a `theorem` and
`lake build` passes.

More: [use Belay with a coding agent](guide/agents.md), the
[surface library](../packages/belay/README.md).
