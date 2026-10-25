set_option doc.verso true

/-! The source positions of a checked SQL documentation block. Native Verso removes the
indentation of the code fence from each line of the block text before it gives the text to a
handler, so a byte offset in the text is not a byte offset in the file. This module recovers the
file offsets from the original lines and refuses to guess when the lines disagree with the
text. -/

namespace Belay.Sqlite.SqlDoc

/-- Where one line of the block text starts: its byte offset in the text, and the byte offset in
the file of its first character. -/
structure LineStart where
  /-- The offset of the line in the block text. -/
  textOffset : Nat
  /-- The offset in the file of the first character of the line in the block text. -/
  fileOffset : Nat
  deriving Repr, BEq

/-- The start of every line of a block text in the file. -/
structure SourceMap where
  /-- The lines, in order. -/
  lines : Array LineStart
  deriving Repr, BEq

/-- Whether the original line is the text line with only spaces before it, which is what
the removal of the fence indentation leaves. -/
def indentedCopy (original text : String) : Bool :=
  let removed := original.toList.length - text.toList.length
  original.toList.drop removed == text.toList && (original.toList.take removed).all (· == ' ')

/-- Pair the original lines with the lines of the block text, with the running offsets, or
{lean}`(none : Option (List LineStart))` when a line is not an indented copy of its text line. -/
def pairLines (fileOffset : Nat) : List String → List String → Nat → Option (List LineStart)
  | [], [], _ => some []
  | original :: originals, text :: texts, textOffset =>
    if indentedCopy original text then
      let removed := original.utf8ByteSize - text.utf8ByteSize
      (pairLines (fileOffset + original.utf8ByteSize + 1) originals texts
        (textOffset + text.utf8ByteSize + 1)).map
        (⟨textOffset, fileOffset + removed⟩ :: ·)
    else none
  | _, _, _ => none

/-- The map of a block text, from the file text that the code block occupies (from the first
character of its first line to the end of its last line, as native Verso reports it) and the
block text. It is none when the original lines are not the text lines with fence indentation,
for example when a future Lean release changes the block text. -/
def SourceMap.ofSource? (blockStart : Nat) (original text : String) : Option SourceMap :=
  (pairLines blockStart (original.splitOn "\n") (text.splitOn "\n") 0).map (⟨·.toArray⟩)

/-- The offset in the file of a byte offset in the block text. An offset after the last line
start belongs to that line. -/
def SourceMap.fileOffset (map : SourceMap) (offset : Nat) : Nat :=
  match map.lines.findRev? (·.textOffset ≤ offset) with
  | some line => line.fileOffset + (offset - line.textOffset)
  | none => offset

/-- The byte range in the file of a half-open byte range of the block text. A range with no
bytes covers one byte, so that an editor can show it. The end is mapped from the last byte of
the range, so a range that ends at the start of a line does not reach into the indentation. -/
def SourceMap.fileRange (map : SourceMap) (start stop : Nat) : Nat × Nat :=
  let first := map.fileOffset start
  (first, max (first + 1) (if start < stop then map.fileOffset (stop - 1) + 1 else first + 1))

end Belay.Sqlite.SqlDoc
