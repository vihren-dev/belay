import Lean

/-! The range of the `deriving instance` command of an instance, from Lean's own parser.

The build products give an instance of a `deriving instance` command only the range of the
class name in the command. The specification of the Lean code store stores the text of the
whole command for such an instance, so the fact reader parses the commands of the file. -/

open Lean

namespace LeanCodeStore

/-- A position as `[line, column]`, lines from 1 and columns in code points. -/
def positionJson (map : FileMap) (pos : String.Pos.Raw) : Array Nat :=
  let position := map.toPosition pos
  #[position.line, position.column]

/-- The `[start, end)` byte ranges of the `deriving instance` commands of a file.

The parser reads the header and then each command in order, as Lean's front end does, so
comments are skipped as whitespace. It uses the final environment of the module: a command whose
syntax depends on a syntax extension that the same file declares after it can parse otherwise
than at elaboration. -/
def derivingCommandRanges (env : Environment) (input : Parser.InputContext) :
    IO (Array (String.Pos.Raw × String.Pos.Raw)) := do
  let (_, headerState, _) ← Parser.parseHeader input
  let context : Parser.ParserModuleContext := { env, options := {} }
  let mut state := headerState
  let mut found := #[]
  while !input.atEnd state.pos do
    let (command, next, messages) := Parser.parseCommand input context state {}
    if next.pos.byteIdx ≤ state.pos.byteIdx then break
    state := next
    if command.getKind == ``Parser.Command.deriving && !messages.hasErrors then
      if let (some first, some last) := (command.getPos?, command.getTailPos?) then
        found := found.push (first, last)
  return found

/-- The command range of each instance with a declaration position in a `deriving instance`
command, as `[line, column, endLine, endColumn]`. -/
def derivingCommands (env : Environment) (source : System.FilePath)
    (instances : Array (Name × Position)) : IO Json := do
  if instances.isEmpty then return Json.mkObj []
  let text ← IO.FS.readFile source
  let input := Parser.mkInputContext text source.toString
  let commands ← derivingCommandRanges env input
  let map := input.fileMap
  let found := instances.filterMap fun (name, position) => do
    let target := map.ofPosition position
    let (first, last) ← commands.find? fun (first, last) =>
      first.byteIdx ≤ target.byteIdx && target.byteIdx < last.byteIdx
    return (name.toString, toJson (positionJson map first ++ positionJson map last))
  return Json.mkObj found.toList

end LeanCodeStore
