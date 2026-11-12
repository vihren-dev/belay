set_option doc.verso true

/-! The expected-text comments of a checked SQL documentation block. The text of a block ends
with a group of standalone {lit}`--` lines when the example states its expected text. Whether a
{lit}`--` starts a comment depends on the SQL lexical state, so this module reads the text one
character at a time and does not search for substrings. -/

namespace Belay.Sqlite.SqlDoc

/-- Where the reader is in the SQL text. Quote modes end at their closing character; a doubled
quote leaves and re-enters the mode, which keeps the escaped quote inside the literal. -/
inductive LexicalState where
  /-- Outside every string, quoted name and comment. -/
  | code
  /-- Inside {lit}`'...'`. -/
  | singleQuoted
  /-- Inside {lit}`"..."`. -/
  | doubleQuoted
  /-- Inside a backtick name. -/
  | backtickQuoted
  /-- Inside {lit}`[...]`. -/
  | bracketQuoted
  /-- Inside {lit}`/* ... */`, which SQLite ends at the end of the text when unclosed. -/
  | blockComment
  /-- Inside a {lit}`--` comment, which ends at the next newline. -/
  | lineComment
  deriving BEq

/-- One line of the text: its characters, and whether the reader was outside strings, quoted
names and comments where the line starts. -/
structure SourceLine where
  /-- The characters of the line, without the newline. -/
  text : String
  /-- Whether the line starts in {name}`LexicalState.code`. -/
  startsInCode : Bool

/-- The state after one character; the second character decides the two-character tokens
{lit}`--`, {lit}`/*` and {lit}`*/`. The result also tells whether the second character is part
of the token and must be skipped. -/
def advance (state : LexicalState) (current : Char) (following : Option Char) : LexicalState × Bool :=
  match state with
  | .code =>
    if current == '\'' then (.singleQuoted, false)
    else if current == '"' then (.doubleQuoted, false)
    else if current == '`' then (.backtickQuoted, false)
    else if current == '[' then (.bracketQuoted, false)
    else if current == '-' && following == some '-' then (.lineComment, true)
    else if current == '/' && following == some '*' then (.blockComment, true)
    else (.code, false)
  | .singleQuoted => (if current == '\'' then .code else state, false)
  | .doubleQuoted => (if current == '"' then .code else state, false)
  | .backtickQuoted => (if current == '`' then .code else state, false)
  | .bracketQuoted => (if current == ']' then .code else state, false)
  | .blockComment =>
    if current == '*' && following == some '/' then (.code, true) else (state, false)
  | .lineComment => (state, false)

/-- The reader while it scans the text: the lexical state, whether the next character is the
second character of a two-character token, and the line so far. -/
structure Reader where
  /-- The lexical state after the characters read. -/
  state : LexicalState := .code
  /-- Whether the next character completes a two-character token. -/
  completesToken : Bool := false
  /-- Whether the line in progress started in {name}`LexicalState.code`. -/
  lineStartsInCode : Bool := true
  /-- The characters of the line in progress, last first. -/
  current : List Char := []
  /-- The lines that a newline has ended, in order. -/
  finished : List SourceLine := []

/-- Read one character with the character after it. A newline ends the line and a {lit}`--`
comment; every other state continues on the next line. -/
def Reader.read (reader : Reader) (character : Char) (following : Option Char) : Reader :=
  if character == '\n' then
    let next := if reader.state == .lineComment then LexicalState.code else reader.state
    { state := next, lineStartsInCode := next == .code,
      finished := reader.finished ++ [{ text := String.ofList reader.current.reverse,
                                        startsInCode := reader.lineStartsInCode }] }
  else if reader.completesToken then
    { reader with completesToken := false, current := character :: reader.current }
  else
    let (state, completesToken) := advance reader.state character following
    { reader with state, completesToken, current := character :: reader.current }

/-- The lines of the text, each with the lexical state where it starts. A string or block
comment can span lines. The text always gives at least one line; text that ends with a newline
gives a last, empty line. -/
def sourceLines (body : String) : List SourceLine :=
  let characters := body.toList
  let reader := (characters.zip ((characters.drop 1).map some ++ [none])).foldl
    (fun reader (character, following) => reader.read character following) ({} : Reader)
  reader.finished ++ [{ text := String.ofList reader.current.reverse, startsInCode := reader.lineStartsInCode }]

/-- Whether the character is SQL white space, which SQLite skips between tokens. -/
def isSqlSpace (character : Char) : Bool :=
  character == ' ' || character == '\t' || character == '\n' || character == '\r' || character == '\u000C'

/-- Whether the line has no character except white space. -/
def SourceLine.isBlank (line : SourceLine) : Bool := line.text.toList.all isSqlSpace

/-- Whether the line is a comment of its own: it starts outside strings and comments, and its
first character after white space starts {lit}`--`. -/
def SourceLine.isStandaloneComment (line : SourceLine) : Bool :=
  line.startsInCode && (line.text.toList.dropWhile isSqlSpace).take 2 == ['-', '-']

/-- The text of an expected line: the white space before the marker and the marker are removed,
then at most one following space. The rest is kept, including trailing spaces. A final carriage
return belongs to the line ending and is not part of the text. -/
def SourceLine.expectedText (line : SourceLine) : String :=
  let withoutReturn := if line.text.toList.getLast? == some '\r' then line.text.dropEnd 1 |>.copy else line.text
  match (withoutReturn.toList.dropWhile isSqlSpace).drop 2 with
  | ' ' :: rest => String.ofList rest
  | rest => String.ofList rest

/-- The expected text of a block: the final contiguous group of standalone {lit}`--` lines,
after the white space lines at the end are ignored. The lines of the group are joined by
newlines, with no newline at the end. Earlier comments, comments that follow SQL on their line,
and any {lit}`--` inside a string, quoted name or block comment are not part of it. A text with
no such group expects the empty text. For example,
the text {lit}`SELECT 1;`, a newline, {lit}`-- 1`, a newline, {lit}`-- 2` gives the text {lit}`1`, a
newline, {lit}`2`. -/
def expectedComments (body : String) : String :=
  let reversed := (sourceLines body).reverse.dropWhile SourceLine.isBlank
  let group := reversed.takeWhile SourceLine.isStandaloneComment
  "\n".intercalate (group.reverse.map SourceLine.expectedText)

end Belay.Sqlite.SqlDoc
