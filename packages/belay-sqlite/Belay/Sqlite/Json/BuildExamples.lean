import Belay.Sqlite.Json.ExampleSupport
import Belay.Sqlite.Json.JsonApply
import Belay.Sqlite.ExprEval

set_option doc.verso true

/-! Checked examples of the JSON functions that build or edit text (ADR 0015, slice 3), and of
the JSON subtype of their arguments. Each result was checked on native SQLite 3.51.0, one
statement per line. -/

namespace Belay.Sqlite.Json.BuildExamples

open Belay.Sqlite Belay.Sqlite.Json Belay.Sqlite.Json.ExampleSupport

/-- A TEXT argument without the JSON subtype. -/
def plain (text : String) : Value × Bool := (sqlText text, false)

/-- A TEXT argument with the JSON subtype, as a direct call of {lit}`json` gives it. -/
def marked (text : String) : Value × Bool := (sqlText text, true)

/-- An INTEGER argument. -/
def number (value : Int) : Value × Bool := (.integer value, false)

-- json_array and json_quote: text is quoted unless it is JSON; REALs by %!0.15g.
#guard givesText (apply .array [number 1, (.real (2.5 : Float).toBits, false), plain "a\"b", (.null, false),
  marked "[1]", plain "[1]", (.real (1e300 : Float).toBits, false)]) "[1,2.5,\"a\\\"b\",null,[1],\"[1]\",1.0e+300]"
#guard givesText (apply .quote [(.real (0.1 : Float).toBits, false)]) "0.1"
#guard givesText (apply .quote [plain "a\u0001\n"]) "\"a\\u0001\\n\""
#guard fails (apply .array [(.blob [1], false)]) .blobArgument

-- json_object: labels must be TEXT; an odd count fails; duplicates stay; an infinity.
#guard givesText (apply .object [plain "a", number 1, plain "b", marked "{}", plain "a",
  (.real (1.0 / 0.0 : Float).toBits, false)]) "{\"a\":1,\"b\":{},\"a\":9.0e+999}"
#guard fails (apply .object [plain "a"]) .objectArgumentCount
#guard fails (apply .object [number 1, number 1]) .labelNotText

-- json_set, json_insert and json_replace: each mode; created substructure; ignored paths.
#guard givesText (apply .set [plain "[1,2]", plain "$[#]", number 3, plain "$[5]", number 9]) "[1,2,3]"
#guard givesText (apply .set [plain "{}", plain "$.a.b", number 1]) "{\"a\":{\"b\":1}}"
#guard givesText (apply .set [plain "[]", plain "$[0].a", number 1]) "[{\"a\":1}]"
#guard givesText (apply .set [plain "{}", plain "$.a[5]", number 1]) "{}"
#guard givesText (apply .set [plain "{\"a\":1}", plain "$.a.b", number 2]) "{\"a\":1}"
#guard givesText (apply .set [plain "{\"a\":1}", plain "$", plain "x"]) "\"x\""
#guard givesText (apply .insert [plain "{\"a\":1}", plain "$.a", number 5, plain "$.c", plain "x"])
  "{\"a\":1,\"c\":\"x\"}"
#guard givesText (apply .replace [plain "{\"a\":1}", plain "$.a", marked "[2]", plain "$.b", number 3])
  "{\"a\":[2]}"
#guard givesText (apply .set [plain "[1]", plain "$[0]", (.real (-1.0 / 0.0 : Float).toBits, false)]) "[-9e999]"
#guard fails (apply .set [plain "{\"a\":1}", plain "$a", number 2]) (.badPath (utf8 "$a"))
#guard fails (apply .set [plain "{\"a\":1}", plain "$a"]) (.editArgumentCount (utf8 "set"))
#guard fails (apply .set [plain "[1]", plain "$[0]", marked "[1"]) .malformed

-- json_remove: in turn; a NULL path or $ gives NULL.
#guard givesText (apply .remove [plain "[1,2,3]", plain "$[1]", plain "$[0]"]) "[3]"
#guard gives (apply .remove [plain "[1,2,3]", plain "$"]) .null
#guard gives (apply .remove [plain "{\"a\":1}", plain "$.a", (.null, false)]) .null

-- json_patch: RFC 7396, null removes, objects merge, a patch that is no object replaces.
#guard givesText (apply .patch [plain "{\"a\":1,\"b\":{\"c\":2}}",
  plain "{\"a\":null,\"b\":{\"d\":3},\"e\":{\"f\":null,\"g\":1}}"]) "{\"b\":{\"c\":2,\"d\":3},\"e\":{\"g\":1}}"
#guard givesText (apply .patch [plain "[1]", plain "{\"a\":1}"]) "{\"a\":1}"
#guard givesText (apply .patch [plain "{\"a\":1}", plain "[2]"]) "[2]"

-- json_pretty and json_error_position.
#guard givesText (apply .pretty [plain "{\"a\":[1,2,{}],\"b\":[]}"])
  "{\n    \"a\": [\n        1,\n        2,\n        {}\n    ],\n    \"b\": []\n}"
#guard givesText (apply .pretty [plain "[1,[2]]", plain "\t"]) "[\n\t1,\n\t[\n\t\t2\n\t]\n]"
#guard gives (apply .errorPosition [plain "[1]"]) (.integer 0)
#guard fails (apply .errorPosition [plain "{\"a\":"]) .unmodeledPosition

/-- The JSON subtype in evaluation: {lit}`json_array(json('[1]'), json_extract('[[2],"[3]"]', '$[0]'),
json_extract('[[2],"[3]"]', '$[1]'))` is {lit}`[[1],[2],"[3]"]`: the selected array is JSON and the
selected string is text. -/
def subtypeCall : Resolved.Expr :=
  .json .array (.cons (.json .json (.cons (.literal (sqlText "[1]")) .nil))
    (.cons (.json .extract (.cons (.literal (sqlText "[[2],\"[3]\"]")) (.cons (.literal (sqlText "$[0]")) .nil)))
    (.cons (.json .extract (.cons (.literal (sqlText "[[2],\"[3]\"]")) (.cons (.literal (sqlText "$[1]")) .nil)))
    .nil)))

example : (subtypeCall.evaluate 0 []).1 = sqlText "[[1],[2],\"[3]\"]" := by decide +kernel

example : givesText (apply .set [plain "{\"a\":1}", plain "$.b[0]", number 2]) "{\"a\":1,\"b\":[2]}" = true := by
  decide +kernel

example : givesText (apply .patch [plain "{\"a\":{\"b\":1}}", plain "{\"a\":{\"b\":null,\"c\":2}}"])
    "{\"a\":{\"c\":2}}" = true := by
  decide +kernel

end Belay.Sqlite.Json.BuildExamples
