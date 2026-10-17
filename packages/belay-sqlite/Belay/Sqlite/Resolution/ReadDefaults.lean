import Belay.Sqlite.Resolution.Defaults
import Belay.Sqlite.StoreValue

set_option doc.verso true

/-! Defaults for fields absent from old records after ADD COLUMN. SQLite uses
{lit}`sqlite3ValueFromExpr` here, which differs from expression evaluation for
INSERT. Affinity conversion still uses the shared {name}`Belay.Sqlite.storeValue`. -/

namespace Belay.Sqlite

/-- Read a numeric default using SQLite's literal-value path. Decimal text that
is not an in-range unsigned integer keeps its spelling under TEXT affinity.
An oversized hexadecimal token stays text, while unary minus converts that text
to zero. Negating the hexadecimal minimum integer produces a REAL value.
Separators are removed as the parser does. For example,
{lean}`readNumericDefault .text "1.50" false` reads the spelling {lit}`1.50`
for a TEXT column.
Use {name}`queryNumeric` for INSERT expression evaluation instead. -/
def readNumericDefault (affinity : Affinity) (token : String) (negated : Bool) : Value :=
  let text := String.ofList (token.toList.filter (· ≠ '_'))
  let value := match numericValue text false with
    | .integer integer =>
      if negated then
        if integer == -(2 ^ 63 : Int) then .real (9223372036854775808.0 : Float).toBits
        else .integer (-integer)
      else .integer integer
    | .hexTooBig => if negated then .integer 0 else .text text.toUTF8.toList
    | .real =>
      let bytes := ((if negated then "-" else "") ++ text).toUTF8.toList
      if affinity == .blob then
        if text.toList.any (fun c => c == '.' || c == 'e' || c == 'E') then realLiteral text.toList negated
        else numericText bytes
      else .text bytes
  storeValue affinity value

/-- The value that old rows read for a written default after ADD COLUMN, stored with the
affinity: numeric tokens use {name}`readNumericDefault`; other literal forms use
{name}`literalDefault`. Time and compound expressions are model restrictions. -/
def writtenReadBack (affinity : Affinity) (written : Syntax.DefaultExpression) : Except ValueIssue Value :=
  match written.expression with
  | .numeric text | .positive (.numeric text) => .ok (readNumericDefault affinity text false)
  | .negate (.numeric text) => .ok (readNumericDefault affinity text true)
  | .null | .string _ | .blob _ | .currentTime _ | .identifier ..
  | .negate _ | .positive _ | .compare .. | .and .. | .or .. | .not _
  | .isNull .. | .callStar _ | .call .. | .arithmetic .. | .cast .. | .qualified .. =>
    (literalDefault written.expression).map (storeValue affinity)

/-- The resolved default of a written DEFAULT for a column of the affinity
({name}`ColumnDefault`), evaluated once: a time keyword is {lean}`DefaultForm.clock`; a
literal keeps its INSERT value ({name}`literalDefault`, or its {lit}`hex literal too big`
error) and its read-back value ({name}`writtenReadBack`). A default that the model does
not describe is {lean}`(none : Option ColumnDefault)`; resolution refuses it with a
model restriction ({lit}`modeledDefault`). -/
def resolveColumnDefault (affinity : Affinity) (written : Syntax.DefaultExpression) : Option ColumnDefault :=
  let form : Option DefaultForm := match written.expression with
    | .currentTime keyword => some (.clock (timeKeywordNamed keyword))
    | .null | .numeric _ | .string _ | .blob _ | .identifier .. | .negate _ | .positive _
    | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call ..
    | .arithmetic .. | .cast .. | .qualified .. =>
      match literalDefault written.expression, writtenReadBack affinity written with
      | .ok value, .ok readBack => some (.literal (.value value) readBack)
      | .error (.prepare (.hexLiteralTooBig text)), .ok readBack => some (.literal (.hexLiteralTooBig text) readBack)
      | .ok _, .error _ | .error _, _ => none
  form.map fun form => { form, sourceText := written.sourceText }

/-- Whether the column's default is a time keyword, such as {lit}`DEFAULT CURRENT_TIMESTAMP`,
whose value depends on the statement's clock. ADD COLUMN with such a default fails on a
populated table ({lit}`Cannot add a column with non-constant default`), and INSERT gives an
omitted value the statement's clock text. -/
def CatalogColumn.clockDefault (column : CatalogColumn) : Bool :=
  match column.defaultValue with
  | some { form := .clock _, .. } => true
  | some { form := .literal .., .. } | none => false

/-- Read a column's default for a field absent from an old record, stored with the
column's affinity: NULL without a default, the stored read-back value of a literal
default, and a model restriction for a time keyword default, which ADD COLUMN handles
apart ({name}`CatalogColumn.clockDefault`). For omitted INSERT values use
{name}`defaultValue`, whose numeric errors have different semantics. -/
def readDefaultValue (column : CatalogColumn) : Except ValueIssue Value :=
  match column.defaultValue with
  | none => .ok .null
  | some { form := .literal _ readBack, .. } => .ok (storeValue column.affinity readBack)
  | some { form := .clock _, .. } => .error (.restriction [] .unmodeledDefault)

end Belay.Sqlite
