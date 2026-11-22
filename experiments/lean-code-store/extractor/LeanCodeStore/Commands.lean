import Lean

/-! The range of the `deriving instance` command of an instance, from Lean's own parser.

The build products give an instance of a `deriving instance` command only the range of the
class name in the command. The specification of the Lean code store stores the text of the
whole command for such an instance, so the fact reader parses the command at that place. -/

open Lean

namespace LeanCodeStore

/-- The byte offsets of each occurrence of `deriving` in a text, in increasing order. -/
def derivingOffsets (text : String) : Array Nat := Id.run do
  let bytes := text.toUTF8
  let word := "deriving".toUTF8
  let mut found := #[]
  for i in [0:bytes.size - word.size + 1] do
    if (List.range word.size).all fun j => bytes[i + j]! == word[j]! then
      found := found.push i
  return found

/-- A position as `[line, column]`, lines from 1 and columns in code points. -/
def positionJson (map : FileMap) (pos : String.Pos.Raw) : Array Nat :=
  let position := map.toPosition pos
  #[position.line, position.column]

/-- The range of the `deriving instance` command that contains a position, if one does.

The candidates are the occurrences of `deriving` before the position, nearest first. The first
candidate where Lean's parser reads a `deriving` command without errors that contains the
position is the command. An occurrence in a comment inside the command does not parse, so the
search continues to the next candidate. -/
def derivingCommand? (env : Environment) (input : Parser.InputContext) (offsets : Array Nat)
    (position : Position) : Option Json := Id.run do
  let target := input.fileMap.ofPosition position
  let context : Parser.ParserModuleContext := { env, options := {} }
  for start in offsets.reverse do
    if start > target.byteIdx then continue
    let (command, _, messages) := Parser.parseCommand input context { pos := ⟨start⟩ } {}
    let some first := command.getPos? | continue
    let some last := command.getTailPos? | continue
    if command.getKind == ``Parser.Command.deriving && !messages.hasErrors
        && first.byteIdx ≤ target.byteIdx && target.byteIdx < last.byteIdx then
      return some (toJson (positionJson input.fileMap first ++ positionJson input.fileMap last))
  return none

/-- The command range of each instance with a declaration range in a `deriving instance` command. -/
def derivingCommands (env : Environment) (source : System.FilePath)
    (instances : Array (Name × Position)) : IO Json := do
  let text ← IO.FS.readFile source
  let input := Parser.mkInputContext text source.toString
  let offsets := derivingOffsets input.inputString
  let found := instances.filterMap fun (name, position) =>
    (derivingCommand? env input offsets position).map fun range => (name.toString, range)
  return Json.mkObj (found.toList)

end LeanCodeStore
