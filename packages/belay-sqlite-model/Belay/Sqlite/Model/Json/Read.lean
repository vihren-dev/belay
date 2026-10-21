import Belay.Sqlite.Model.Json.ReadScalar

set_option doc.verso true

/-! SQLite's JSON reader for arrays, objects and a whole text ({lit}`jsonTranslateTextToBlob`
and {lit}`jsonConvertTextToBlob` in 3.51.0). The reader accepts JSON5: comments, trailing
commas, unquoted labels, single quotes and the JSON5 numbers. Its recursion takes
explicit fuel; the fuel of {lit}`parseJsonText` is larger than the number of nested
calls that any text can need. -/

namespace Belay.Sqlite.Model.Json

/-- The greatest nesting depth of arrays and objects ({lit}`JSON_MAX_DEPTH`). -/
def maxDepth : Nat := 1000

/-- The result of one call of the reader at a position. SQLite returns the position
after the value or a negative code; the codes for {lit}`}`, {lit}`]`, {lit}`,` and
{lit}`:` keep the position of that byte ({lit}`pParse->iErr`). -/
inductive ReadOutcome where
  /-- A value, the position after it, and whether SQLite met no JSON5 form in the value
  and the white space before it ({lit}`pParse->hasNonstd` stays clear). -/
  | value (node : JsonNode) (next : Nat) (standard : Bool)
  /-- The end of the text (code 0). -/
  | endOfInput
  /-- A syntax error (code -1). -/
  | syntaxError
  /-- A {lit}`}` at a position (code -2). -/
  | closeBrace (position : Nat)
  /-- A {lit}`]` at a position (code -3). -/
  | closeBracket (position : Nat)
  /-- A {lit}`,` at a position (code -4). -/
  | comma (position : Nat)
  /-- A {lit}`:` at a position (code -5). -/
  | colon (position : Nat)

/-- Whether every byte from {lit}`start` up to, not including, {lit}`stop` is a JSON
space byte ({name}`isJsonSpace`). SQLite skips these bytes without the JSON5 flag; any
other white space or comment goes through {lit}`json5Whitespace`, which sets it. -/
def onlyJsonSpace (text : Array UInt8) (start stop : Nat) : Bool := (slice text start stop).all isJsonSpace

/-- The outcome of a scalar reader: a value or a syntax error. {lit}`spaceStandard` tells
whether the white space before the value is standard. -/
def scalarOutcome (spaceStandard : Bool) : Option ScalarRead → ReadOutcome
  | some read => .value read.node read.next (spaceStandard && read.standard)
  | none => .syntaxError

/-- The first position at or after {lit}`position` that does not continue an unquoted
label: a label byte that does not start JSON5 white space, or a {lit}`\uXXXX` escape
(which makes the label {lit}`JSONB_TEXTJ`). The result also tells whether an escape
was seen. -/
def bareLabelEnd (text : Array UInt8) : Nat → Nat → Bool → Nat × Bool
  | 0, position, escaped => (position, escaped)
  | fuel + 1, position, escaped =>
    let byte := byteAt text position
    if isLabelPart byte && json5SpaceEnd text position == position then
      bareLabelEnd text fuel (position + 1) escaped
    else if byte == 92 && byteAt text (position + 1) == 117 && hasHexDigits text (position + 2) 4 then
      bareLabelEnd text fuel (position + 1) Bool.true
    else (position, escaped)

/-- Read an unquoted JSON5 label after the white space at {lit}`position`: it starts
with a label start byte or a {lit}`\uXXXX` escape. The payload is the label bytes as
written. -/
def readBareLabel (text : Array UInt8) (position : Nat) : Option (JsonNode × Nat) :=
  let start := json5SpaceEnd text position
  let byte := byteAt text start
  let startsEscaped := byte == 92 && byteAt text (start + 1) == 117 && hasHexDigits text (start + 2) 4
  if isLabelStart byte || startsEscaped then
    let (stop, escaped) := bareLabelEnd text (text.size + 1) (start + 1) startsEscaped
    let payload := slice text start stop
    some (if escaped then .textj payload else .text payload, stop)
  else none

/-- Whether a node can be an object label: one of the string nodes. -/
def isLabelNode (node : JsonNode) : Bool := node.labelText.isSome

mutual
/-- Read one value at {lit}`position` after JSON5 white space, at a nesting
{lit}`depth`. A {lit}`{` or {lit}`[` that would pass {name}`maxDepth` is an error. -/
def readValue (text : Array UInt8) : Nat → Nat → Nat → ReadOutcome
  | 0, _, _ => .syntaxError
  | fuel + 1, position, depth =>
    let start := json5SpaceEnd text position
    let spaceStandard := onlyJsonSpace text position start
    let byte := byteAt text start
    if byte == 123 then
      if depth + 1 > maxDepth then .syntaxError
      else readMembers text fuel (start + 1) (depth + 1) [] spaceStandard
    else if byte == 91 then
      if depth + 1 > maxDepth then .syntaxError
      else readItems text fuel (start + 1) (depth + 1) [] spaceStandard
    else if byte == 125 then .closeBrace start
    else if byte == 93 then .closeBracket start
    else if byte == 44 then .comma start
    else if byte == 58 then .colon start
    else if byte == 0 then .endOfInput
    else if byte == 34 || byte == 39 then scalarOutcome spaceStandard (readString text start)
    else if byte == 43 || byte == 45 || byte == 46 || isAsciiDigit byte then
      scalarOutcome spaceStandard (readNumber text start)
    else scalarOutcome spaceStandard (readLiteral text start)

/-- Read the next array element at {lit}`position`; {lit}`items` holds the earlier
elements in reverse order, and {lit}`standard` tells whether the array is standard so
far. A {lit}`]` here closes the array; after a comma it is a JSON5 trailing comma. -/
def readItems (text : Array UInt8) : Nat → Nat → Nat → List JsonNode → Bool → ReadOutcome
  | 0, _, _, _, _ => .syntaxError
  | fuel + 1, position, depth, items, standard =>
    match readValue text fuel position depth with
    | .closeBracket spot =>
      .value (.array items.reverse) (spot + 1) (standard && items.isEmpty && onlyJsonSpace text position spot)
    | .value node next valueStandard => readItemEnd text fuel next depth (node :: items) (standard && valueStandard)
    | .endOfInput | .syntaxError | .closeBrace _ | .comma _ | .colon _ => .syntaxError

/-- Read the separator after an array element at {lit}`position`: a comma continues,
a {lit}`]` closes the array, and anything else is an error. -/
def readItemEnd (text : Array UInt8) : Nat → Nat → Nat → List JsonNode → Bool → ReadOutcome
  | 0, _, _, _, _ => .syntaxError
  | fuel + 1, position, depth, items, standard =>
    match readValue text fuel position depth with
    | .comma spot => readItems text fuel (spot + 1) depth items (standard && onlyJsonSpace text position spot)
    | .closeBracket spot => .value (.array items.reverse) (spot + 1) (standard && onlyJsonSpace text position spot)
    | .value _ _ _ | .endOfInput | .syntaxError | .closeBrace _ | .colon _ => .syntaxError

/-- Read the next object member at {lit}`position`: a label, a colon and a value.
A {lit}`}` here closes the object; after a comma it is a JSON5 trailing comma. The
label is a string, or an unquoted JSON5 label when no value can be read there; another
value as a label is an error. -/
def readMembers (text : Array UInt8) : Nat → Nat → Nat → List (JsonNode × JsonNode) → Bool → ReadOutcome
  | 0, _, _, _, _ => .syntaxError
  | fuel + 1, position, depth, members, standard =>
    let label : Option (JsonNode × Nat × Bool) ⊕ Nat :=
      match readValue text fuel position depth with
      | .closeBrace spot => .inr spot
      | .value node next labelStandard => .inl (if isLabelNode node then some (node, next, labelStandard) else none)
      | .endOfInput | .syntaxError | .closeBracket _ | .comma _ | .colon _ =>
        .inl ((readBareLabel text position).map fun (node, next) => (node, next, Bool.false))
    match label with
    | .inr spot =>
      .value (.object members.reverse) (spot + 1) (standard && members.isEmpty && onlyJsonSpace text position spot)
    | .inl none => .syntaxError
    | .inl (some (label, next, labelStandard)) =>
      match readValue text fuel next depth with
      | .colon spot =>
        match readValue text fuel (spot + 1) depth with
        | .value node after valueStandard =>
          readMemberEnd text fuel after depth ((label, node) :: members)
            (standard && labelStandard && onlyJsonSpace text next spot && valueStandard)
        | .endOfInput | .syntaxError | .closeBrace _ | .closeBracket _ | .comma _ | .colon _ => .syntaxError
      | .value _ _ _ | .endOfInput | .syntaxError | .closeBrace _ | .closeBracket _ | .comma _ => .syntaxError

/-- Read the separator after an object member at {lit}`position`: a comma continues,
a {lit}`}` closes the object, and anything else is an error. -/
def readMemberEnd (text : Array UInt8) : Nat → Nat → Nat → List (JsonNode × JsonNode) → Bool → ReadOutcome
  | 0, _, _, _, _ => .syntaxError
  | fuel + 1, position, depth, members, standard =>
    match readValue text fuel position depth with
    | .comma spot => readMembers text fuel (spot + 1) depth members (standard && onlyJsonSpace text position spot)
    | .closeBrace spot =>
      .value (.object members.reverse) (spot + 1) (standard && onlyJsonSpace text position spot)
    | .value _ _ _ | .endOfInput | .syntaxError | .closeBracket _ | .colon _ => .syntaxError
end

/-- Read a whole JSON text as {lit}`jsonParseFuncArg` and {lit}`jsonConvertTextToBlob`
do: an empty text is malformed; one value, then only JSON5 white space up to the end
or to the first NUL byte. The reader stops at a NUL byte, so bytes after it do not
count. The result is the value and whether SQLite met no JSON5 form in the text
({lit}`pParse->hasNonstd`); {lit}`none` means malformed JSON. -/
def readJsonText (bytes : List UInt8) : Option (JsonNode × Bool) :=
  if bytes.isEmpty then none
  else
    let text := bytes.toArray
    match readValue text (4 * text.size + 8) 0 0 with
    | .value node next standard =>
      let stop := json5SpaceEnd text next
      if byteAt text stop == 0 then some (node, standard && onlyJsonSpace text next stop) else none
    | .endOfInput | .syntaxError | .closeBrace _ | .closeBracket _ | .comma _ | .colon _ => none

/-- Parse a whole JSON text ({name}`readJsonText`) to its value; {lit}`none` means
malformed JSON. -/
def parseJsonText (bytes : List UInt8) : Option JsonNode := (readJsonText bytes).map (·.1)

/-- Whether SQLite's reader accepts the text and meets no JSON5 form on the way:
{lit}`json_valid(text)` (flags 1) is 1 exactly when this is true ({lit}`jsonValidFunc`).
The JSON5 forms are white space other than the four JSON space bytes, comments,
trailing commas, unquoted labels, single quotes, JSON5 escapes and raw control bytes in
strings, JSON5 numbers, and the names of infinity and NaN. -/
def standardJson (bytes : List UInt8) : Bool := (readJsonText bytes).any (·.2)

end Belay.Sqlite.Model.Json
