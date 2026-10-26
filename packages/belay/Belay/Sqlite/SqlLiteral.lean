import Lean.Syntax

set_option doc.verso true

/-! The source range of a byte range of the SQL text in a string literal, so that an error of
the SQL shows at its position in the Lean file. -/

namespace Belay.Sqlite

open Lean

/-- The number of bytes before the text in the source of a string literal whose text is the
bytes between its delimiters: 1 for a plain literal without escapes, and {lit}`n + 2` for a raw
literal with {lit}`n` signs {lit}`#`. For any other literal, {lean}`(none : Option Nat)`. For
example, {assert}`openingSize "r#\"a\"#" "a" = some 3`. -/
def openingSize (atom text : String) : Option Nat :=
  if atom == "\"" ++ text ++ "\"" then some 1
  else match atom.toList with
    | 'r' :: rest =>
      let hashes := "".pushn '#' (rest.takeWhile (· == '#')).length
      if atom == "r" ++ hashes ++ "\"" ++ text ++ "\"" ++ hashes then some (hashes.utf8ByteSize + 2) else none
    | [] => none
    | _ :: _ => none

/-- Whether the bytes, read as the content of a raw literal with {lit}`hashes` signs {lit}`#`,
contain the closing delimiter: a quote followed by that many {lit}`#`. -/
def closesRawLiteral (hashes : Nat) : List UInt8 → Bool
  | [] => false
  | byte :: rest => (byte == 34 && rest.take hashes == List.replicate hashes 35) || closesRawLiteral hashes rest

/-- Whether the replacement of the bytes from {lean}`start` to {lean}`stop` of the literal's text
leaves the literal as it is, with the same end and without escapes. A plain literal accepts no quote
and no backslash. A raw literal with {lit}`n` signs {lit}`#` accepts no quote followed by {lit}`n`
signs {lit}`#`, also not when the text after the range completes it. Both accept no carriage return,
because Lean reads the line end in a literal as a line feed. For example, {lit}`"label"` is no
replacement in {lit}`r"..."` and is one in {lit}`r#"..."#`. -/
def replacementKeepsLiteral (atom text : String) (start stop : Nat) (replacement : String) : Bool :=
  let bytes := text.toUTF8
  let spliced := (bytes.extract 0 start ++ replacement.toUTF8 ++ bytes.extract stop bytes.size).toList
  let keepsEnd :=
    if atom.startsWith "\"" then !spliced.contains 34 && !spliced.contains 92
    else !closesRawLiteral ((atom.toList.drop 1).takeWhile (· == '#')).length spliced
  keepsEnd && !replacement.contains '\r'

/-- The source range of a byte range of a string literal's text, when each byte of the text is a
byte of the source: a raw literal with any number of {lit}`#`, or a plain literal without
escapes ({name}`openingSize`). Otherwise the literal's range. A range without bytes covers one
byte. -/
def textRange (literal : Syntax) (text : String) (start stop : Nat) : Syntax :=
  match literal.getPos?, literal.isStrLit? with
  | some position, some _ =>
    match openingSize (literal.getArg 0).getAtomVal text with
    | some opening =>
      let first : String.Pos.Raw := ⟨position.byteIdx + opening + start⟩
      Syntax.atom (.synthetic first ⟨first.byteIdx + max 1 (stop - start)⟩) ""
    | none => literal
  | some _, none | none, some _ | none, none => literal

end Belay.Sqlite
