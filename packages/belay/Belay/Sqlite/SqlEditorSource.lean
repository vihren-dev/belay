import Belay.Sqlite.SqlLiteral
import Lean.Data.Position

set_option doc.verso true

/-! Map SQL byte ranges to original Lean source so editor requests identify the SQL occurrence.
File and documentation callers can supply the same explicit mapping boundary. -/

namespace Belay.Sqlite
open Lean

/-- SQL text with a mapping from its UTF-8 byte ranges to the current Lean document.
File and documentation callers can supply their own mapping. Return {lean}`none` when an
occurrence has no exact source range; editor information must not guess a location. -/
structure SqlEditorSource where
  /-- The decoded SQL that the translator read. -/
  text : String
  /-- Map a nonempty SQL byte range to the corresponding original source range, or
  {lean}`none` if the bytes cannot be mapped exactly. -/
  range? : Nat → Nat → Option Syntax.Range

/-- Map a raw or unescaped ordinary SQL literal. Escaped literals have no exact token map;
their existing diagnostics still use the whole-literal fallback of {name}`textRange`. -/
def SqlEditorSource.literal (literal : Syntax) (text : String) : SqlEditorSource :=
  { text, range? := fun start stop => do
      if start >= stop || stop > text.utf8ByteSize then none else do
        let position ← literal.getPos?
        let _ ← literal.isStrLit?
        let opening ← openingSize (literal.getArg 0).getAtomVal text
        return { start := ⟨position.byteIdx + opening + start⟩,
                 stop := ⟨position.byteIdx + opening + stop⟩ } }

/-- An original-source identifier for an exactly mapped SQL occurrence. The bytes must agree
with the current document before Lean can hover or color the token. The Lean identifier name
may differ from its SQL spelling, as {lit}`$value` denotes the Lean name {lit}`value`. -/
def SqlEditorSource.identifier? (source : SqlEditorSource) (file : FileMap)
    (start stop : Nat) (name : Name) : Option Syntax := do
  if start >= stop || stop > source.text.utf8ByteSize then none else do
    let range ← source.range? start stop
    if range.start >= range.stop || range.stop.byteIdx > file.source.utf8ByteSize then none else do
      let token : Substring.Raw := ⟨file.source, range.start, range.stop⟩
      let sqlToken : Substring.Raw := ⟨source.text, ⟨start⟩, ⟨stop⟩⟩
      if token.toString != sqlToken.toString then none else
        let leading : Substring.Raw := ⟨file.source, range.start, range.start⟩
        let trailing : Substring.Raw := ⟨file.source, range.stop, range.stop⟩
        some (.ident (.original leading range.start trailing range.stop) token name [])

end Belay.Sqlite
