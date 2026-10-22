import Lean.Syntax

set_option doc.verso true

/-! The source range of a byte range of the SQL text in a string literal, so that an error of
the SQL shows at its position in the Lean file. -/

namespace Belay.Sqlite

open Lean

/-- The delimiters of the string literals whose text is the bytes between them: a plain literal
without escapes, and raw literals with up to two {lit}`#`. -/
def literalDelimiters : List (String × String) :=
  [("\"", "\""), ("r\"", "\""), ("r#\"", "\"#"), ("r##\"", "\"##")]

/-- The source range of a byte range of a string literal's text, when each byte of the text is a
byte of the source: a raw literal, or a plain literal without escapes. Otherwise the literal's
range. A range without bytes covers one byte. -/
def textRange (literal : Syntax) (text : String) (start stop : Nat) : Syntax :=
  match literal.getPos?, literal.isStrLit? with
  | some position, some _ =>
    let atom := (literal.getArg 0).getAtomVal
    match literalDelimiters.find? fun (opening, closing) => atom == opening ++ text ++ closing with
    | some (opening, _) =>
      let first : String.Pos.Raw := ⟨position.byteIdx + opening.utf8ByteSize + start⟩
      Syntax.atom (.synthetic first ⟨first.byteIdx + max 1 (stop - start)⟩) ""
    | none => literal
  | some _, none | none, some _ | none, none => literal

end Belay.Sqlite
