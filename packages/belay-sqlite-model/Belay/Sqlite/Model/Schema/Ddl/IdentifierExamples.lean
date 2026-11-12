import Belay.Sqlite.Model.Shared.Values.Identifier

set_option doc.verso true

/-! Checked examples of names as bytes: SQLite's ASCII-only case folding, the text of a
name for messages, and the source form of the generated input modules. -/

namespace Belay.Sqlite.Model.IdentifierExamples

open Belay.Sqlite.Model

-- ASCII capitals fold; other bytes, also those of non-ASCII letters, stay.
#guard (name! "ÄInvoices").folded == bytes! "Äinvoices"
#guard (name! "Ab_É").sameName (name! "aB_É") && !(name! "É").sameName (name! "é")

end Belay.Sqlite.Model.IdentifierExamples
