import Belay.Sqlite.Resolution.Queries

set_option doc.verso true

/-! Declarative rules of {lit}`SELECT` resolution (ADR 0012, slice 1) and their
proofs. A column reference resolves by {name}`Belay.Sqlite.columnPosition`, whose
rule is in the column specification of ADR 0008; the rules here are the ones that
queries add. -/

namespace Belay.Sqlite

/-- For every list of result column aliases and every term that is not an
identifier: if the term is an integer literal {lit}`k` from 1 to the number of
result columns, it names result column {lit}`k - 1`; if it is an integer literal
outside that range, it names no column and is out of range (SQLite's
{lit}`ORDER BY` or {lit}`GROUP BY` term out of range). -/
theorem namedResult_integer (names : List (Option String)) (term : Syntax.Expr) (number : Int)
    (notIdentifier : ∀ name doubleQuoted, term ≠ .identifier name doubleQuoted)
    (literal : integerLiteral term = some number) :
    namedResult names term =
      if 1 ≤ number ∧ number ≤ (names.length : Int) then some (.ok (number.toNat - 1)) else some (.error ()) := by
  cases term with
  | identifier name doubleQuoted => exact absurd rfl (notIdentifier name doubleQuoted)
  | _ => simp only [namedResult, literal, Option.map_some]; split <;> rfl

/-- For every context, catalog, statement index and {lit}`SELECT`: when the catalog
has no table with the folded name and the name is not reserved for SQLite's own
tables, resolution gives SQLite's {lit}`no such table: %s` and keeps the catalog. -/
theorem resolveSelect_noSuchTable (context : ResolveContext) (catalog : Catalog) (index : Nat)
    (results : List Syntax.ResultColumn) (tableName : String) (filter : Option Syntax.Expr)
    (groupBy : List Syntax.Expr) (orderBy : List Syntax.OrderTerm) (limit offset : Option Syntax.Expr)
    (missing : catalog.findTable tableName = none) (application : reservedName tableName = false) :
    resolveSelect context catalog index results tableName filter groupBy orderBy limit offset =
      .ok (.prepareError (.noSuchTable tableName), catalog) := by
  simp [resolveSelect, missing, application, prepareError]

end Belay.Sqlite
