import DocGen4.DB

/-! Regression for PR #242's doc-gen4 compound-SELECT failure with 532 roots.
This calls the compiled pinned reader, including its parameter binding and
recursive query. Remove it when the pinned upstream query no longer needs our patch. -/

open Lean DocGen4.DB

/-- Require exactly the expected closure, with no duplicate or unrelated modules. -/
def expectClosure (reader : ReadDB) (roots expected : Array Name) : IO Unit := do
  let found ← reader.getTransitiveImports roots
  unless found.size == expected.size && found.all expected.contains && expected.all found.contains do
    throw <| IO.userError s!"Incorrect closure for {roots.size} roots: expected {expected}, got {found}"
  IO.println s!"transitive imports: {roots.size} roots, {found.size} distinct modules"

/-- Exercise the real reader above the failed limit and on shared, cyclic and empty graphs. -/
def main : IO Unit := do
  let path : System.FilePath := "transitive-imports-regression.db"
  let writer ← ensureWriteDb builtinDocstringValues path
  let roots := (Array.range 640).map fun i => Name.mkSimple s!"Root{i}"
  let extras := #[`Shared, `Cycle, `Unrelated]
  for name in roots ++ extras do
    writer.saveModule name.toString none
  writer.saveImport "Root0" `Shared
  writer.saveImport "Root1" `Shared
  writer.saveImport "Shared" `Cycle
  writer.saveImport "Cycle" `Shared
  let reader ← openForReading path builtinDocstringValues
  expectClosure reader #[] #[]
  expectClosure reader #[`Unrelated] #[`Unrelated]
  for size in #[499, 500, 501, 532, 640] do
    let selected := roots.extract 0 size
    let expected := selected ++ #[`Shared, `Cycle]
    expectClosure reader selected expected
    expectClosure reader (selected ++ #[`Root0, `Root1]) expected
