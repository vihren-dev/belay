import RebuildGuide

set_option doc.verso true

/-! The check of the README's wrong rebuild, with the claim of the README's theorem: {lit}`on shop` limits the claim
to the databases of the schema, and the check searches those databases. The README shows this command and its
answer. -/

open Belay.Sqlite
namespace RebuildGuide

/-- The schema of the README, without rows: the tables of {name}`sample`. -/
def shop : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
  CREATE TABLE sessions (id INTEGER PRIMARY KEY,
    customer_id INTEGER NOT NULL REFERENCES customers(id) ON DELETE CASCADE,
    expires_at INTEGER NOT NULL);"

#sql_check makeStrictWrongEnforced preserves allSessions on shop

end RebuildGuide
