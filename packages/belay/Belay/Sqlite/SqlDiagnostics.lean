import Belay.Sqlite.Model.Resolution.ErrorNames
import Belay.Sqlite.Run
import Belay.Sqlite.Translation

set_option doc.verso true

/-! The errors that {lit}`sql! db r"..."` shows in the SQL text, as byte ranges of the text, so
that the elaborator only maps each range into the Lean file. A model restriction has a node path
and shows at the node that the path selects. A prepare error has only the names of its message,
so it shows at the one place of the statement's text that writes that name, or at the statement
when the text writes the name at no place or at more than one place. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model Translation

/-- An error at a half-open UTF-8 byte range of the SQL text, with its message. For example,
{lean}`({ start := 7, stop := 11, message := "no such column: nmae" } : Diagnostic)`. -/
structure Diagnostic where
  /-- The first byte of the range. -/
  start : Nat
  /-- The byte after the range. -/
  stop : Nat
  /-- The message that the user reads. -/
  message : String
  deriving Repr, BEq, Inhabited

/-- The folded name that the text of a range writes ({name}`dequote`,
{name}`Identifier.folded`), or {lean}`(none : Option (List UInt8))` for a string literal, which
starts with {lit}`'` and names nothing. -/
def leafName? (bytes : ByteArray) (range : Nat × Nat) : Option (List UInt8) :=
  let text := (String.fromUTF8? (bytes.extract range.1 range.2)).getD ""
  if text.startsWith "'" then none else some (Identifier.ofString (dequote text)).folded

/-- The ranges of the span that write the name, with ASCII case ignored, each range once
({name}`Span.leaves`, {name}`leafName?`). A qualified name, such as {lit}`t.a`, is one name with
a dot ({name}`ExprError.noSuchColumn`): it also matches a leaf that writes the qualifier, a dot
right after it, and a leaf right after the dot that writes the column, and gives the range of
the two leaves and the dot. A name with three parts, such as {lit}`main.t.a`, matches only a leaf
that writes all of it. -/
def nameRanges (bytes : ByteArray) (span : Span) (name : Identifier) : List (Nat × Nat) :=
  let leaves := span.leaves.toList.eraseDups
  let whole := leaves.filter fun leaf => leafName? bytes leaf == some name.folded
  let qualified := leaves.flatMap fun first => leaves.filterMap fun second =>
    let joined := (leafName? bytes first).bind fun qualifier =>
      (leafName? bytes second).map fun column => qualifier ++ [46] ++ column
    if bytes[first.2]? == some 46 && second.1 == first.2 + 1 && joined == some name.folded then
      some (first.1, second.2)
    else none
  (whole ++ qualified).eraseDups

/-- The range of the name in the statement's span when exactly one range writes it
({name}`nameRanges`). When the text writes the name more than once, for example as an alias and
as a column, only the role tells which one the error is about, so the search gives
{lean}`(none : Option (Nat × Nat))`, as it does when the text does not write the name. -/
def nameRange? (bytes : ByteArray) (span : Span) (name : Identifier) : Option (Nat × Nat) :=
  match nameRanges bytes span name with
  | [range] => some range
  | [] | _ :: _ :: _ => none

/-- The range of the statement in the SQL text. -/
def statementRange (item : Located Syntax.Statement) : Nat × Nat := (item.span.start, item.span.stop)

/-- The prepare error at the name of its message in the statement ({name}`PrepareError.name?`,
{name}`nameRange?`), or at the statement; the message is SQLite's
({name}`PrepareError.message`). -/
def prepareDiagnostic (bytes : ByteArray) (item : Located Syntax.Statement) (error : PrepareError) :
    Diagnostic :=
  let (start, stop) := (error.name?.bind (nameRange? bytes item.span)).getD (statementRange item)
  { start, stop, message := error.message }

/-- The restriction at the node that its path selects in the statement ({name}`Span.select`),
with the model's reason ({name}`NodeRestriction.reason`): SQLite runs such SQL, so it gives no
message. -/
def restrictionDiagnostic (item : Located Syntax.Statement) (restriction : NodeRestriction) :
    Diagnostic :=
  let (start, stop) := item.span.select restriction.path
  { start, stop, message := restriction.reason }

/-- The errors of the statements, resolved in order from the state with the surface's context
({name}`resolveStatement`, {name}`runContext`), step for step as {name}`resolveFrom` resolves
them: each prepare error, and the first model restriction. Resolution stops at the restriction,
so the statements after it show no error. For example, the text {lit}`SELECT nmae FROM t`
against a catalog with the table {lit}`t(a)` gives {lit}`no such column: nmae` at the bytes
from 7 to 11. -/
def scriptDiagnostics (state : ResolveState) (bytes : ByteArray) :
    List (Located Syntax.Statement) → List Diagnostic
  | [] => []
  | item :: rest => match resolveStatement runContext state item.value with
    | .error restriction => [restrictionDiagnostic item restriction]
    | .ok (resolved, next) =>
      (resolved.prepareError?.map (prepareDiagnostic bytes item)).toList ++
        scriptDiagnostics next bytes rest

end Belay.Sqlite
