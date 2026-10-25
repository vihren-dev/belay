import Belay.Sqlite.Values

set_option doc.verso true

/-! Expression hints for small SQL samples. The traversal reuses the model's literal reader
and proposes column names and values without making assumptions about the database. -/

namespace Belay.Sqlite.Sampling

open Belay.Sqlite.Model

/-- Names and values that suggest small candidate schemas and rows. A qualified column
keeps its source name; an unqualified column has none. These are search hints, not facts
about the database or evidence for a claim. Use an empty record when no SQL is available. -/
structure Hints where
  /-- Column references in source order, with an optional table or alias qualifier. -/
  columns : List (Option Identifier × Identifier) := []
  /-- Literal values in source order, interpreted by the model's existing literal reader. -/
  values : List Value := []

/-- Combine hints in source order; schema construction can then remove duplicate names. -/
def Hints.append (first second : Hints) : Hints :=
  { columns := first.columns ++ second.columns, values := first.values ++ second.values }

/-- Read a literal through the model. An expression outside that reader's domain adds no
value hint; this refusal has no effect on the meaning of the original SQL. -/
private def literalHint (expression : Syntax.Expr) : Hints :=
  { values := (literalDefault expression).toOption.toList }

mutual
/-- Collect column names and literal values from an SQL expression. Subquery bodies are
collected separately from the statement's indexed subquery list. Parameters contribute
through their bound values, rather than through their numeric slot indexes. -/
def expressionHints : Syntax.Expr → Hints
  | expression@(.null) | expression@(.numeric _) | expression@(.string _) | expression@(.blob _) =>
    literalHint expression
  | .identifier name quote =>
    if quote == .none && (name.isKeyword (bytes! "true") || name.isKeyword (bytes! "false")) then
      literalHint (.identifier name quote)
    else { columns := [(none, name)] }
  | .qualified source column _ => { columns := [(some source, column)] }
  | expression@(.negate operand) | expression@(.positive operand) =>
    (literalHint expression).append (expressionHints operand)
  | .compare _ left right | .and left right | .or left right | .arithmetic _ left right
  | .concatenate left right => (expressionHints left).append (expressionHints right)
  | .not operand | .isNull operand _ | .cast operand _ | .collate operand _
  | .inQuery operand .. => expressionHints operand
  | .call _ arguments | .caseOf arguments _ => expressionListHints arguments
  | .inList operand values _ => (expressionHints operand).append (expressionListHints values)
  | .between operand low high _ =>
    ((expressionHints operand).append (expressionHints low)).append (expressionHints high)
  | .raise _ (some message) => expressionHints message
  | .raise _ none => {}
  | .parameter _ | .currentTime _ | .callStar _ | .exists _ | .subquery _ => {}
termination_by expression => sizeOf expression

/-- Combine expression hints in list order, using the same traversal for every clause. -/
def expressionListHints : List Syntax.Expr → Hints
  | [] => {}
  | first :: rest => (expressionHints first).append (expressionListHints rest)
termination_by expressions => sizeOf expressions
end

/-- Hints from explicit result expressions. Stars add no column names because their width
is a property of the database, which the checker is trying to discover. -/
def resultHints (columns : List Syntax.ResultColumn) : Hints :=
  columns.foldl (fun hints column => match column with
    | .expression expression _ _ => hints.append (expressionHints expression)
    | .star | .sourceStar _ => hints) {}

end Belay.Sqlite.Sampling
