import LeanCodeStore.Module

/-! Command line of the fact reader of the Lean code store prototype. -/

open Lean

/-- Write the facts of one module to a JSON file. `LEAN_PATH` must name the compiled libraries.

One process reads one module: the environment extensions are loaded, so Lean cannot free the
imported data and cannot run the initializers of a second import in the same process. -/
unsafe def main (arguments : List String) : IO UInt32 := do
  let [module, output] := arguments
    | IO.eprintln "Usage: lean-code-store-facts MODULE OUTPUT.json"
      return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  LeanCodeStore.extractModule module.toName output
  return 0
