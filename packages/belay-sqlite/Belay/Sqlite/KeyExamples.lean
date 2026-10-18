import Belay.Sqlite.LiteralPreservationLaws

set_option doc.verso true

/-! Examples of unique key equality (ADR 0012, amendment 4; slice 5a), checked by
{lit}`#guard`: SQLite's comparison of stored cells with the BINARY collation, NULL,
composite keys, and the uniqueness check of a table. -/

namespace Belay.Sqlite.KeyExamples
open Belay.Sqlite LiteralData

/-- The REAL value {lit}`1.0`. -/
def realOne : Value := .real 0x3FF0000000000000

-- Numbers by value, TEXT and BLOB by bytes, different storage classes never, NULL never.
#guard keyCellsEqual (.integer 1) realOne
#guard keyCellsEqual (.text [97]) (.text [97])
#guard !keyCellsEqual (.text [97]) (.text [65])
#guard !keyCellsEqual (.integer 1) (.text [49])
#guard !keyCellsEqual (.text [49]) (.blob [49])
#guard !keyCellsEqual .null .null

/-- A row of two cells. -/
def row (rowid : Int) (first second : Value) : Row := { rowid, values := [first, second] }

-- A composite key conflicts only when every cell conflicts; a NULL cell never does.
#guard keyEqual [0, 1] (row 1 (.integer 1) (.text [120])) (row 2 realOne (.text [120]))
#guard !keyEqual [0, 1] (row 1 (.integer 1) (.text [120])) (row 2 (.integer 1) (.text [121]))
#guard !keyEqual [0, 1] (row 1 (.integer 1) .null) (row 2 (.integer 1) .null)
-- The uniqueness check of a table over its rows.
#guard uniqueRows [0] [row 1 (.text [97]) .null, row 2 (.text [65]) .null]
#guard !uniqueRows [0] [row 1 (.integer 1) .null, row 2 realOne .null]
#guard uniqueRows [0] [row 1 (.integer 1) .null, row 2 (.text [49]) .null]

end Belay.Sqlite.KeyExamples
