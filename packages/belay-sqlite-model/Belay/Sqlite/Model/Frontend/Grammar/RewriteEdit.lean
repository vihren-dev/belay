import Belay.Sqlite.Model.Shared.Syntax.SyntaxTokens

set_option doc.verso true

namespace Belay.Sqlite.Model.Syntax

/-- The name as it stands in a text with the quote: the quote characters around it, and a quote
character in the name doubled. For example, {lean}`Identifier.ofString "a\"b"` in double quotes is
{lit}`"a""b"`. -/
def QuoteKind.render (quote : QuoteKind) (name : String) : String :=
  match quote with
  | .none => name
  | .double => "\"" ++ name.replace "\"" "\"\"" ++ "\""
  | .bracket => "[" ++ name ++ "]"
  | .backtick => "`" ++ name.replace "`" "``" ++ "`"
  | .single => "'" ++ name.replace "'" "''" ++ "'"

end Belay.Sqlite.Model.Syntax
