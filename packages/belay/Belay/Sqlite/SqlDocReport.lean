import Lean.Elab.DocString
import Belay.Sqlite.SqlDocSource

set_option doc.verso true

/-! Where the errors of a checked SQL documentation block are shown. An error about the SQL
text is shown at the original occurrence in the file when the lines of the block can be matched
with the file, and otherwise at the whole block with a note. -/

namespace Belay.Sqlite.SqlDoc

open Lean Elab Term

/-- The code block of a documentation comment: its syntax, and the map from its text to the
file when native Verso's text is the file's lines with the fence indentation removed. -/
structure BlockSource where
  /-- The string literal of the block text. -/
  block : StrLit
  /-- The file offsets of the lines of the text, if they are known. -/
  map : Option SourceMap

/-- The source of a code block: the lines of the file that the block covers, matched with the
text that Verso gives ({name}`SourceMap.ofSource?`). -/
def BlockSource.ofBlock (block : StrLit) : TermElabM BlockSource := do
  let source := (← getFileMap).source
  let map := do
    let first ← block.raw.getPos?
    let last ← block.raw.getTailPos?
    SourceMap.ofSource? first.byteIdx (String.Pos.Raw.extract source first last) block.getString
  return { block, map }

/-- The syntax where a byte range of the block text is shown: the range in the file, or the
whole block when the file range is not known. -/
def BlockSource.reference (source : BlockSource) (start stop : Nat) : Syntax :=
  match source.map with
  | some map =>
    let (first, last) := map.fileRange start stop
    Syntax.atom (.synthetic ⟨first⟩ ⟨last⟩) ""
  | none => source.block

/-- Log an error at a byte range of the SQL text. Without a file range, the note says why the
error is at the whole block. -/
def BlockSource.reportSql (source : BlockSource) (start stop : Nat) (message : String) : TermElabM Unit :=
  let note := if source.map.isSome then "" else
    "\nLean did not give the position of this SQL in the file, so the error is shown at the whole block."
  logErrorAt (source.reference start stop) (message ++ note)

/-- Log an error at the whole block, such as a result that differs from the expectation. -/
def BlockSource.reportBlock (source : BlockSource) (message : String) : TermElabM Unit :=
  logErrorAt source.block message

end Belay.Sqlite.SqlDoc
