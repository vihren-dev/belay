import Belay.Sqlite.Model.Resolution.RewriteText
import Belay.Sqlite.Model.Resolution.Checks

set_option doc.verso true

/-! The text of a CHECK constraint after a rename (ADR 0019, D4). SQLite keeps the source text of a CHECK
constraint, rewrites the name tokens in it, and reports the label of an unnamed constraint as the dequoted
text, so the label changes with the text. A constraint with a {lit}`CONSTRAINT name` keeps its label and its
condition. The conditions are resolved forms that read columns by position, so a rename changes no condition. -/

namespace Belay.Sqlite.Model

open Syntax

/-- SQLite's {lit}`sqlite3Dequote` of a text: a text that starts with a quote ({lit}`'`, {lit}`"`, {lit}`` ` ``
or {lit}`[`) becomes the characters up to the closing quote, a doubled quote standing for one quote; another text
stays. A label is the dequoted text of the constraint, so a text that starts with a quoted table name
({lit}`"u v".a > 0`) has the label {lit}`u v`. For example, the dequoted text {lit}`"a b".c` is {lit}`a b`. -/
def dequoteLabel (text : String) : String :=
  let bytes := text.toUTF8.toList
  match bytes with
  | [] => text
  | first :: rest =>
    let close : Option UInt8 :=
      if first == 39 || first == 34 || first == 96 then some first else if first == 91 then some 93 else none
    match close with
    | none => text
    | some close =>
      let rec scan : List UInt8 → List UInt8
        | [] => []
        | byte :: more =>
          if byte == close then
            match more with
            | next :: after => if next == close then close :: scan after else []
            | [] => []
          else byte :: scan more
      (String.fromUTF8? (ByteArray.mk (scan rest).toArray)).getD text

/-- Whether the text has a double quote that no name token of the text covers: a double-quoted string in the
CHECK constraint, or one inside a single-quoted string. SQLite rewrites such a string to single quotes at every
rename ({lit}`renameQuotefix`), which the model does not write into the text, so a rename of a table with such a
text is a restriction. For example, {lit}`a > 0 AND "x" = 1` has a loose quote when {lit}`"x"` is no column. -/
def CheckText.hasLooseQuote (text : CheckText) : Bool :=
  text.text.toUTF8.toList.zipIdx.any fun (byte, index) =>
    byte == 34 && !(text.names.any fun name => name.start ≤ index && index < name.stop)

/-- The code of a label target in the path of a token: the table is 0 and the column {lit}`k` is {lit}`k + 1`.
It lets {lit}`CheckText.rename` reuse the token rewrite of {name}`SourceText.replaceTokens`. -/
def LabelTarget.code : LabelTarget → Nat
  | .table => 0
  | .column position => position + 1

/-- The text of a CHECK constraint with the tokens of the target written with the new name: the same rewrite
as for the text of a result column. None when the tokens do not lie in the text. -/
def CheckText.rename (target : LabelTarget) (style : RenameStyle) (new : Identifier) (text : CheckText) :
    Option CheckText := do
  let source : SourceText := { text := text.text, tokens := text.names.map fun name =>
    { paths := [[name.target.code]], start := name.start, stop := name.stop, quote := name.quote } }
  let renamed ← source.replaceTokens fun token =>
    if token.paths == [[target.code]] then
      let quote := style.quote token.quote
      some (quote, quote.render new.text)
    else none
  pure { text := renamed.text, names := (text.names.zip renamed.tokens).map fun (name, token) =>
    { name with start := token.start, stop := token.stop, quote := token.quote } }

/-- The constraint after a rename of the target: its text and its label follow the tokens; a constraint
without a text keeps its label. None when the tokens do not lie in the text. -/
def CheckConstraint.rename (target : LabelTarget) (style : RenameStyle) (new : Identifier)
    (check : CheckConstraint) : Option CheckConstraint :=
  match check.source with
  | none => some check
  | some text => (text.rename target style new).map fun renamed =>
    { check with source := some renamed, label := dequoteLabel renamed.text }

end Belay.Sqlite.Model
