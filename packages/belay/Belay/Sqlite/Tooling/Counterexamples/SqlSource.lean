import Belay.Sqlite.Frontend.Embedding.SqlSource

set_option doc.verso true

/-! Source hints for SQL search and replay. Lean expression metadata preserves literal text
and positions across named definitions without changing a script or database's meaning.
Consumers must validate the text against the actual value before presenting a replay. -/

namespace Belay.Sqlite

open Lean

/-- The metadata key for the SQL text of a database's schema, on a database that the checker
generated on the schema of a {lit}`db!` constant. The text can also have rows, which the
construction of the generated database leaves out. -/
def schemaSourceKey : Name := `Belay.Sqlite.source.schema

/-- Attach the SQL text of a database's schema ({name}`schemaSourceKey`) to a generated
database as definitionally irrelevant metadata. The text is a hint for the construction of a
replay, which validates it. -/
def withSchemaText (text : String) (expression : Expr) : Expr :=
  mkMData (KVMap.empty.insert schemaSourceKey (.ofString text)) expression

/-- Original literal text and range recovered from an annotation. A caller must retranslate
or execute the text and compare it with the represented script or database before replay. -/
structure SourceText where
  /-- The decoded text of the SQL literal. -/
  text : String
  /-- The original literal syntax; imported definitions can refer to another source file. -/
  literal : Syntax
  /-- The source file for the literal range; it may differ from the current consumer file. -/
  fileName : String
  /-- The annotated value expression, whose actual value must agree with the text. -/
  expression : Expr

/-- Read the outer annotation for the selected script/database key. Missing annotations
return none, so handwritten values remain usable through explicit replay or schema inputs. -/
def sourceText? (key : Name) : Expr → Option SourceText
  | .mdata data expression => do
    let text ← data.get? (α := String) key
    pure { text, literal := data.getSyntax sourceRangeKey, fileName := data.getString sourceFileKey, expression }
  | _ => none

/-- The number of definition unfoldings that a search for the SQL text of a term makes before it gives up.
128 covers the definitions of a project, which name each other a few levels deep. -/
def sourceUnfoldings : Nat := 128

/-- Recover source through a finite number of named-definition and lambda expansions.
The returned expression is the supplied value, including parameter applications and explicit
rebinding. Text remains a hint; callers must validate it against that complete expression.
Use an explicit text input when the default {name}`sourceUnfoldings` expansions cannot recover a source. -/
def sourceOf (key : Name) (expression : Expr) (fuel : Nat := sourceUnfoldings) : MetaM (Option SourceText) := do
  let rec visit : Nat → Expr → MetaM (Option SourceText)
    | 0, _ => pure none
    | fuel + 1, current => do
      if let some source := sourceText? key current then return some { source with expression }
      match current with
      | .mdata _ body => visit fuel body
      | .letE _ _ value body _ => visit fuel (body.instantiate1 value)
      | _ =>
        let head := current.getAppFn
        let arguments := current.getAppArgs
        if head.isLambda then return ← visit fuel (head.beta arguments)
        if head.isConstOf ``Script.withValues && !arguments.isEmpty then
          return ← visit fuel (arguments[0]!)
        let .const name levels := head | return none
        let some info := (← getEnv).find? name | return none
        let some body := info.value? | return none
        visit fuel ((body.instantiateLevelParams info.levelParams levels).beta arguments)
  visit fuel expression

end Belay.Sqlite
