import Belay.Sqlite.Model.Resolution.RewriteQuery

set_option doc.verso true

/-! Rewrite the name tokens of the text of a result column (ADR 0019, D4). SQLite keeps the text of an
unaliased expression as the name of a view column, and a rename writes the new name into that text. The
tokens that the frontend records ({name}`Belay.Sqlite.Model.Syntax.SourceText`) say which bytes of the text are a name and which
nodes of the object it is, so the rewrite replaces the bytes of the tokens that have the node of the edit, and
moves the tokens behind them. -/

namespace Belay.Sqlite.Model.Syntax

/-- Replace the bytes of some name tokens of a text. The function says, for a token, the quote and the
text that replace it, or none to keep it. The tokens must lie in text order without overlap; a text
whose tokens do not, or whose bytes are no text, gives none. The tokens behind a replaced token move by
the difference of the lengths. -/
def SourceText.replaceTokens (change : NameToken → Option (QuoteKind × String)) (text : SourceText) :
    Option SourceText := do
  let bytes := text.text.toUTF8
  let mut cursor := 0
  let mut out : ByteArray := ByteArray.empty
  let mut tokens : List NameToken := []
  for token in text.tokens do
    if token.start < cursor || token.stop < token.start || bytes.size < token.stop then none
    out := out ++ bytes.extract cursor token.start
    let start := out.size
    match change token with
    | none => out := out ++ bytes.extract token.start token.stop
    | some (_, replacement) => out := out ++ replacement.toUTF8
    let quote := (change token).elim token.quote Prod.fst
    tokens := tokens ++ [{ token with start, stop := out.size, quote }]
    cursor := token.stop
  out := out ++ bytes.extract cursor bytes.size
  let rewritten ← String.fromUTF8? out
  pure { text := rewritten, tokens }

/-- Whether the token is the name at the path of the edit, for the text of the result column at the path
{lit}`column` (a path of the object as written, such as {lit}`[0, 2, 0]` for the expression of the third
column of the query of the statement): a token of the expression itself lists its paths below the
expression, and a token of a subquery of the text lists its paths below the subquery
{lit}`[8, index]`. -/
def NameToken.isEditedAt (edit : NameEdit) (column : List Nat) (token : NameToken) : Bool :=
  token.paths.any fun path => edit.path == (match token.subquery with
    | none => column ++ path
    | some index => [8, index] ++ path)

/-- The text with the name tokens at the path of the edit written with the new name. -/
def SourceText.renameAt (edit : NameEdit) (column : List Nat) (text : SourceText) : Option SourceText :=
  text.replaceTokens fun token =>
    if token.isEditedAt edit column then
      let quote := edit.style.quote token.quote
      some (quote, quote.render edit.new.text)
    else none

end Belay.Sqlite.Model.Syntax
