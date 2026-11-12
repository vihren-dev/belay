set_option doc.verso true

/-! The comments of an SQL file, found the way SQLite's tokenizer finds them (ADR 0017, S7).
The file markers of {lit}`sql_file` and {lit}`sql_module` are comments, so a marker-like text in
a string, a quoted name or a block comment must not count. The scan is on UTF-8 bytes, like
the parser's ranges, and needs no parse tree. -/

namespace Belay.Sqlite

/-- A comment of the SQL text, as the half-open UTF-8 byte range of its characters. A line
comment ends before its newline. -/
structure SqlComment where
  /-- The byte of the first {lit}`-` or {lit}`/`. -/
  start : Nat
  /-- The byte after the comment. -/
  stop : Nat
  /-- Whether the comment is a {lit}`--` line comment, not a block comment. -/
  isLine : Bool
  deriving Repr, BEq, Inhabited

/-- The byte after the quoted text that starts at {lit}`start` with the quote byte; a doubled
quote stays inside. An unterminated quote ends at the end of the text. -/
private def quotedStop (bytes : ByteArray) (start : Nat) (quote : UInt8) : Nat := Id.run do
  let mut index := start + 1
  while index < bytes.size do
    if bytes[index]! == quote then
      if bytes[index + 1]? == some quote then index := index + 2 else return index + 1
    else index := index + 1
  return bytes.size

/-- The first byte at or after {lit}`from` that is {lit}`target`, or the end of the text. -/
private def findByte (bytes : ByteArray) (target : UInt8) (start : Nat) : Nat := Id.run do
  let mut index := start
  while index < bytes.size && bytes[index]! != target do index := index + 1
  return index

/-- The byte after the block comment that starts at {lit}`start`, or the end of the text when it
is not closed. -/
private def blockStop (bytes : ByteArray) (start : Nat) : Nat := Id.run do
  let mut index := start + 2
  while index < bytes.size do
    if bytes[index]! == 42 && bytes[index + 1]? == some 47 then return index + 2
    index := index + 1
  return bytes.size

/-- Every comment of the text outside single-quoted strings, double-quoted and backtick names,
and bracketed names, in text order. For example, in {lit}`SELECT '--x' -- y` the one comment
is {lit}`-- y`. -/
def sqlComments (bytes : ByteArray) : Array SqlComment := Id.run do
  let mut comments := #[]
  let mut index := 0
  while index < bytes.size do
    let byte := bytes[index]!
    if byte == 39 || byte == 34 || byte == 96 then
      index := quotedStop bytes index byte
    else if byte == 91 then
      index := min bytes.size (findByte bytes 93 (index + 1) + 1)
    else if byte == 45 && bytes[index + 1]? == some 45 then
      let stop := findByte bytes 10 index
      comments := comments.push { start := index, stop, isLine := true }
      index := stop
    else if byte == 47 && bytes[index + 1]? == some 42 then
      let stop := blockStop bytes index
      comments := comments.push { start := index, stop, isLine := false }
      index := stop
    else index := index + 1
  return comments

/-- Whether the byte is a space, tab, carriage return or newline. -/
def isSqlSpace (byte : UInt8) : Bool := byte == 32 || byte == 9 || byte == 13 || byte == 10

/-- The end of a statement's range without the comments and spaces that the parser leaves in it
after its last token. A statement without a final semicolon can carry a trailing comment, which
is not part of the statement and can hold a marker. -/
def statementContentStop (bytes : ByteArray) (comments : Array SqlComment) (start stop : Nat) : Nat := Id.run do
  let mut end_ := stop
  let mut changed := true
  while changed do
    changed := false
    while end_ > start && isSqlSpace bytes[end_ - 1]! do
      end_ := end_ - 1
      changed := true
    if let some comment := comments.find? (fun comment => comment.stop == end_ && start ≤ comment.start) then
      end_ := comment.start
      changed := true
  return end_

end Belay.Sqlite
