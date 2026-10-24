import Belay.Sqlite.Model.Resolution.CommonTableScope

set_option doc.verso true

/-! SQLite's special binding of a recursive source in the trailing UNION terms of a
CTE. This binding happens before ordinary WITH lookup, including inner name shadowing. -/

namespace Belay.Sqlite.Model

/-- Separate a CTE's nonrecursive anchor from its trailing recursive UNION terms.
A term binds an unqualified direct FROM reference to the CTE being expanded when the
operator is the last UNION or UNION ALL operator. The walk stops at the first term
without that binding. A second direct reference in one term is a SQLite error.
This follows {lit}`resolveFromTermToCte`; it is not a search of arbitrary name text. -/
def commonTableRecursiveTerms (written : List Syntax.Subquery) (definition : Syntax.CommonTable)
    (query : Syntax.Subquery) : Except CommonTableError (Syntax.Subquery × List Nat) := do
  let some compound := query.compound | return (query, [])
  let some (lastOperator, _) := compound.rest.getLast? | return (query, [])
  unless lastOperator == .union || lastOperator == .unionAll do return (query, [])
  let mut recursive : List Nat := []
  for (operator, index) in compound.rest.reverse do
    if operator != lastOperator then break
    let some term := written[index]? | break
    let bound := (term.source.toList ++ term.joins.map (·.source)).filter fun source =>
      source.query.isNone && source.table.sameName definition.name
    if bound.isEmpty then break
    if bound.length > 1 then throw (.repeatedTable definition.name)
    recursive := recursive ++ [index]
  let anchor := { compound with rest := compound.rest.filter fun (_, index) => !recursive.contains index }
  return ({ query with compound := some anchor }, recursive)

end Belay.Sqlite.Model
