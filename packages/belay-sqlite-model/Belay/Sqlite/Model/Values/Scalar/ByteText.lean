set_option doc.verso true

/-! Text as bytes (ADR 0013, step 8): the ASCII case folding and NUL termination that the
SQLite readers of JSON, dates and identifiers share, and a literal for fixed byte texts.
SQLite's text may be invalid UTF-8, so the model compares bytes. -/

namespace Belay.Sqlite.Model

/-- The bytes before the first NUL: what SQLite reads from a value as a C string
({lit}`sqlite3_value_text`). Without a NUL, every byte. -/
def bytesBeforeNul (bytes : List UInt8) : List UInt8 := bytes.takeWhile (· != 0)

end Belay.Sqlite.Model
