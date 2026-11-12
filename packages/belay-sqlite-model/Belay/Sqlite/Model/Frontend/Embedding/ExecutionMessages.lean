import Belay.Sqlite.Model.Shared.Execution.Output

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The message for a function that fails while the statement runs, such as a JSON function
with malformed JSON. -/
def functionFailedMessage : String :=
  "a function of the statement failed, for example on malformed JSON; the model does not keep " ++
    "SQLite's message for it. Run the statement in the sqlite3 shell to see that message"

end Belay.Sqlite.Model
