-- Claims/Schema.lean
import Belay
open Belay.Sqlite

/-- The schema of the application before the migration that is in work: the database that
the statements of `db/schema.sql` build from the empty database. The search for
counterexamples reads the SQL of the file. -/
def shop : Database := (Database.empty.run (sql_file "db/schema.sql")).db
