import Belay.Sqlite.Model.Json.ExampleSupport
import Belay.Sqlite.Model.Json.Jsonb
import Belay.Sqlite.Model.Json.Valid

set_option doc.verso true

/-! Checked examples of the JSONB encoder, of SQLite's quick and full checks of a BLOB, and of
the BLOB arguments of the JSON functions (ADR 0015, slice 4). Each result was checked on
native SQLite 3.51.0 ({lit}`hex(jsonb(...))` and {lit}`json_valid(x, 4)` and
{lit}`json_valid(x, 8)`), one statement per line. -/

namespace Belay.Sqlite.Model.Json.JsonbExamples

open Belay.Sqlite.Model Belay.Sqlite.Model.Json Belay.Sqlite.Model.Json.ExampleSupport

/-- The JSONB of a JSON text, as {lit}`jsonb` gives it for TEXT, or none for malformed text. -/
def jsonbOf (text : String) : Option (List UInt8) := (parseJsonText (utf8 text)).map encodeNode

-- Each node type keeps its payload; JSON5 forms keep their own types.
#guard jsonbOf "[1,\"a\",{\"b\":null}]" == some [0x8b, 0x13, 0x31, 0x17, 0x61, 0x3c, 0x17, 0x62, 0x00]
#guard jsonbOf "0x1F" == some [0x44, 0x30, 0x78, 0x31, 0x46]
#guard jsonbOf ".5" == some [0x26, 0x2e, 0x35]
#guard jsonbOf "Infinity" == some [0x55, 0x39, 0x65, 0x39, 0x39, 0x39]
#guard jsonbOf "+5" == some [0x13, 0x35]
#guard jsonbOf "\"a\\nb\"" == some [0x48, 0x61, 0x5c, 0x6e, 0x62]
#guard jsonbOf "\"a\\x41\"" == some [0x59, 0x61, 0x5c, 0x78, 0x34, 0x31]
-- The smallest header: the size in the type byte up to 11, else one or two size bytes.
#guard jsonbHeader 7 11 == [0xb7] && jsonbHeader 7 12 == [0xc7, 12] && jsonbHeader 11 300 == [0xdb, 1, 0x2c]
#guard (jsonbOf "[1,1,1,1,1,1]").map (·.take 2) == some [0xcb, 12]

-- The quick check: the header must fill the BLOB, and a short BLOB that starts like JSON
-- text must pass the full check.
#guard isJsonb [0x13, 0x31] && !isJsonb [0x5b, 0x31, 0x5d] && !isJsonb [] && !isJsonb [0x13]
#guard isJsonb [0xc7, 1, 0x61] && !isJsonb [0x31, 0x32]
-- The full check reads each payload: an INT of digits, a FLOAT with a point or an exponent.
#guard jsonbValid [0x23, 0x2d, 0x30].toArray 8 0 3 1 && !jsonbValid [0x23, 0x2d, 0x61].toArray 8 0 3 1
#guard jsonbValid [0x35, 0x31, 0x65, 0x35].toArray 10 0 4 1 && !jsonbValid [0x25, 0x31, 0x2e].toArray 8 0 3 1
#guard !jsonbValid [0x2c, 0x13, 0x31].toArray 8 0 3 1
-- The model reads JSONB only in the encoding of its tree.
#guard match readBlob [0x2b, 0x13, 0x31] with
  | .tree node => encodeNode node == [0x2b, 0x13, 0x31]
  | .notJsonb | .undescribed => false
#guard match readBlob [0xc7, 1, 0x61] with
  | .undescribed => true
  | .tree _ | .notJsonb => false
-- json_valid of BLOBs: flag 4 is the quick check, flag 8 the full one, and a BLOB that is not
-- JSONB is read as text.
#guard gives (jsonValid (.blob [0x5b, 0x31, 0x5d]) (.integer 1)) (.integer 1)
#guard gives (jsonValid (.blob [0x13, 0x31]) (.integer 4)) (.integer 1)
#guard gives (jsonValid (.blob [0x13, 0x31]) (.integer 1)) (.integer 0)
#guard gives (jsonValid (.blob [0x23, 0x2d, 0x61]) (.integer 8)) (.integer 0)

example : jsonbOf "{\"k\":[true,false,null,1.0,-2]}" =
    some [0xcc, 0x0d, 0x17, 0x6b, 0xab, 0x01, 0x02, 0x00, 0x35, 0x31, 0x2e, 0x30, 0x23, 0x2d, 0x32] := by
  decide +kernel

end Belay.Sqlite.Model.Json.JsonbExamples
