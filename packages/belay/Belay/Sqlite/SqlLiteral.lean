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
