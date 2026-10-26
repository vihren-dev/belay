import Belay.Sqlite.Translation.Expressions

set_option doc.verso true

/-! The name tokens of the source text of a result column. SQLite uses the text of an unaliased
expression as the name of a view column, and a rename rewrites the name tokens of that text, so
the syntax keeps where each name stands in the text, how it was quoted, and the node path that
the name trace reports for it ({name}`Belay.Sqlite.Model.Syntax.NameToken`). The translator
reads the paths from the ranges of the expression and of the subqueries inside it. -/

namespace Belay.Sqlite.Translation

open Belay.Sqlite.Model

/-- Whether the characters after the opening quote hold one quoted name, closed by
{lit}`close` at the last character; a doubled closing quote belongs to the name. For example,
{lean}`quotedNameEnds '"' "a\"\"b\"".toList` is {lean}`true`. -/
def quotedNameEnds (close : Char) : List Char → Bool
  | [] => false
  | [last] => last == close
  | first :: second :: rest =>
    if first == close then (second == close && quotedNameEnds close rest) else quotedNameEnds close (second :: rest)

/-- Whether a text is exactly one name token of SQLite's tokenizer: an unquoted name or a name in
double quotes, brackets or backticks. A keyword has the form of an unquoted name. For example,
{lean}`isNameToken "\"b c\""` is {lean}`true` and {lean}`isNameToken "a.b"` is {lean}`false`. -/
def isNameToken (text : String) : Bool :=
  match text.toList with
  | [] => false
  | '[' :: rest => rest.getLast? == some ']' && !(rest.dropLast.contains ']')
  | '"' :: rest => quotedNameEnds '"' rest
  | '`' :: rest => quotedNameEnds '`' rest
  | first :: rest =>
    let nameChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '$' || c.toNat ≥ 128
    (first.isAlpha || first == '_' || first.toNat ≥ 128) && rest.all nameChar

/-- The nodes of a range tree whose text is one name token, with the path of each from the root,
the first byte and the byte after, in path order. A node and its part can have the same range,
as an identifier and its name do. -/
partial def Span.nameNodes (tree : SqlTree) (span : Span) (path : List Nat := []) : Array (List Nat × Nat × Nat) :=
  let below := (span.parts.zipIdx.map fun (part, step) => part.nameNodes tree (path ++ [step])).flatten
  if isNameToken (tree.slice span.start span.stop) then #[(path, span.start, span.stop)] ++ below else below

/-- The number of subqueries listed so far in the statement. -/
def subqueryCount : TranslateM Nat := do
  return ((← get).active.map (·.items.size)).getD 0

/-- A name range of the text, in the statement's bytes, with the paths of the nodes that have it. -/
structure NameRange where
  /-- The index of the subquery that holds the nodes, or none for the expression itself. -/
  subquery : Option Nat
  /-- The first byte. -/
  begins : Nat
  /-- The byte after. -/
  ends : Nat
  /-- The paths of the nodes with this range, in path order. -/
  paths : List (List Nat)

/-- Add a node to the ranges: to the range that it has, else as a new range. -/
def NameRange.add (ranges : Array NameRange) (subquery : Option Nat) (path : List Nat) (begins ends : Nat) :
    Array NameRange :=
  match ranges.findIdx? fun found => found.subquery == subquery && found.begins == begins && found.ends == ends with
  | some index => ranges.modify index fun found => { found with paths := found.paths ++ [path] }
  | none => ranges.push { subquery, begins, ends, paths := [path] }

/-- The name tokens of the text of an expression, in text order. The expression has the range
tree {lit}`span`, and the subqueries from index {lit}`first` on were mapped for it, so their
names are in the text too. Offsets count from the first byte of the expression. A range tree holds
some ranges more than once, such as the range of an absent alias or of the single argument of a
call and of the list around it, so a token lists the path of each node with its range, and a
client takes the token that has the path of an occurrence. -/
def expressionNameTokens (tree : SqlTree) (start stop : Nat) (span : Span) (first : Nat) :
    TranslateM (List Syntax.NameToken) := do
  let items := (((← get).active.map (·.items)).getD #[]).extract first
  let mut ranges : Array NameRange := #[]
  for (path, begins, ends) in span.nameNodes tree do
    ranges := NameRange.add ranges none path begins ends
  for (item, offset) in items.zipIdx do
    if let some located := item then
      for (path, begins, ends) in located.span.nameNodes tree do
        ranges := NameRange.add ranges (some (first + offset)) path begins ends
  let inside := ranges.filter fun found => start ≤ found.begins && found.ends ≤ stop
  return (inside.qsort (·.begins < ·.begins)).toList.map fun found =>
    { subquery := found.subquery, paths := found.paths, start := found.begins - start, stop := found.ends - start,
      quote := quoteKind (tree.slice found.begins found.ends) }

end Belay.Sqlite.Translation
