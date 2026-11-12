-- Claims/Schema.lean
import Belay
open Belay.Sqlite

/-- The schema of the application before the migration that is in work: the SQL of
`db/schema.sql` as text, which the search for counterexamples needs. -/
def shop : Database := db! r"
CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
CREATE TABLE sessions (id INTEGER PRIMARY KEY,
  customer_id INTEGER NOT NULL REFERENCES customers(id) ON DELETE CASCADE,
  expires_at INTEGER NOT NULL);"

/-- The text above and `db/schema.sql` build the same database. The build fails when
they differ. -/
theorem shop_is_schema_file :
    (Database.empty.run (sql_file "db/schema.sql")).db = shop := by
  decide +kernel
