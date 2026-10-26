import Belay.Sqlite.Translation.Expressions

set_option doc.verso true

/-! The name tokens of the source text of a result column. SQLite uses the text of an unaliased
expression as the name of a view column, and a rename rewrites the name tokens of that text, so
the syntax keeps where each name stands in the text, how it was quoted, and the node paths that
include the one the name trace reports for it ({name}`Belay.Sqlite.Model.Syntax.NameToken`). The
translator reads the paths from the ranges of the expression and of the subqueries inside it,
at the nodes that it marked as names ({lit}`Span.isName`). -/

namespace Belay.Sqlite.Translation

open Belay.Sqlite.Model

/-- The nodes of a range tree that are name tokens ({name}`Span.isName`), with the path of each from
the root, the first byte and the byte after, in path order. A node and its part can have the same
range, as an identifier and its name do. -/
partial def Span.nameNodes (span : Span) (path : List Nat := []) : Array (List Nat × Nat × Nat) :=
  let below := (span.parts.zipIdx.map fun (part, step) => part.nameNodes (path ++ [step])).flatten
  if span.isName then #[(path, span.start, span.stop)] ++ below else below

/-- Run the action with the name tokens of result columns recorded, as in the body of a stored view,
and restore the setting after it. -/
def recordingNameTokens (action : TranslateM α) : TranslateM α := do
  let around := (← get).nameTokens
  modify fun scope => { scope with nameTokens := true }
  let result ← action
  modify fun scope => { scope with nameTokens := around }
  return result

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
some ranges more than once, such as an identifier and its two parts, so a token lists the path of
each name node with its range, and a client takes the token that has the path of an occurrence. -/
def expressionNameTokens (tree : SqlTree) (start stop : Nat) (span : Span) (first : Nat) :
    TranslateM (List Syntax.NameToken) := do
  let items := (((← get).active.map (·.items)).getD #[]).extract first
  let mut ranges : Array NameRange := #[]
  for (path, begins, ends) in span.nameNodes do
    ranges := NameRange.add ranges none path begins ends
  for (item, offset) in items.zipIdx do
    if let some located := item then
      for (path, begins, ends) in located.span.nameNodes do
        ranges := NameRange.add ranges (some (first + offset)) path begins ends
  let inside := ranges.filter fun found => start ≤ found.begins && found.ends ≤ stop
  return (inside.qsort (·.begins < ·.begins)).toList.map fun found =>
    { subquery := found.subquery, paths := found.paths, start := found.begins - start, stop := found.ends - start,
      quote := quoteKind (tree.slice found.begins found.ends) }

end Belay.Sqlite.Translation
