import Belay

/-! Syntax part of the corrected balance example, compiled by the surface success test. -/

set_option doc.verso true
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace BalanceExample

/-- The named source of the ledger queries. -/
def ledgerRef : Syntax.TableReference := {table := name! "ledger", alias := none}

/-- The table-info source with the literal ledger argument. -/
def pragmaRef : Syntax.TableReference := {table := name! "pragma_table_info", alias := none, arguments := some [.string (bytes! "ledger")]}

/-- The guard excludes cells outside the inclusive trillion-cent range. -/
def rangeSyntax : Syntax.Expr := .between (.identifier (name! "cents") .none)
  (.negate (.numeric "1000000000000")) (.numeric "1000000000000") true

/-- The resolved range check keeps the column affinity and collation. -/
def rangeResolved (index : Nat) (cell : CatalogColumn) : Resolved.Expr :=
  .not (.and
    (.compare .ge (some cell.affinity) (.column index) (.literal (.integer (-1000000000000))) cell.collation)
    (.compare .le (some cell.affinity) (.column index) (.literal (.integer 1000000000000)) cell.collation))

/-- The pragma predicate compares its name field with exact text bytes. -/
def nameSyntax (name : List UInt8) : Syntax.Expr := .compare .eq (.identifier (name! "name") .none) (.string name)

/-- The pragma name field uses BINARY comparison and BLOB affinity. -/
def nameResolved (name : List UInt8) : Resolved.Expr := .compare .eq (some .blob) (.column 1) (.literal (.text name)) .binary

/-- The declared type check uses the exact text INTEGER. -/
def typeSyntax : Syntax.Expr := .compare .eq (.identifier (name! "type") .none) (.string (bytes! "INTEGER"))

/-- The cents metadata predicate requires both its name and its declared type. -/
def typedSyntax : Syntax.Expr := .and (nameSyntax (bytes! "cents")) typeSyntax

/-- The resolved cents metadata predicate compares name and type fields. -/
def typedResolved : Resolved.Expr := .and (nameResolved (bytes! "cents")) (.compare .eq (some .blob) (.column 2) (.literal (.text (bytes! "INTEGER"))) .binary)

/-- The syntax of SELECT 1 from one source with an optional condition. -/
def oneQuery (source : Syntax.TableReference) (filter : Option Syntax.Expr) : Syntax.Subquery :=
  {columns := [.expression (.numeric "1") none "1"], source := some source, filter,
    joins := [], groupBy := [], orderBy := [], limit := none, offset := none, parent := none}

/-- The row-count subquery of the guard. -/
def countSyntax : Syntax.Subquery :=
  {columns := [.expression (.callStar "count") none "count(*)"], source := some ledgerRef,
    joins := [], filter := none, groupBy := [], orderBy := [], limit := none, offset := none, parent := none}

/-- The four guard subqueries in their syntax order. -/
def balanceQueries : List Syntax.Subquery := [oneQuery ledgerRef (some rangeSyntax), countSyntax,
  oneQuery pragmaRef (some (nameSyntax (bytes! "account"))), oneQuery pragmaRef (some typedSyntax)]

/-- The query scope with no outer sources or result aliases. -/
def around (pending : List PendingSource) (scope : Scope) : QueryScope :=
  {scope, pending, outer := 0, outerAliases := [], aliases := []}

/-- A named table before its join condition is resolved. -/
def tablePending (position : Nat) : List PendingSource := [{item := .table position, kind := .inner, condition := .none}]

/-- Table-info rows before their join condition is resolved. -/
def pragmaPending (rows : List (List Value)) : List PendingSource :=
  [{item := .pragma (pragmaSource pragmaRef (bytes! "ledger") tableInfoNames rows).1, kind := .inner, condition := .none}]

/-- The source scope of the named ledger table. -/
def ledgerScope (catalog : Catalog) (position : Nat) (table : CatalogTable) : QueryScope :=
  around (tablePending position) (tableScope catalog ledgerRef position table)

/-- The source scope of the ledger metadata. -/
def pragmaScope (rows : List (List Value)) : QueryScope :=
  around (pragmaPending rows) (tableInfoScope pragmaRef (bytes! "ledger") rows)

/-- The resolved query that finds cells outside the accepted range. -/
def rangeQuery (position index : Nat) (cell : CatalogColumn) : Resolved.Query :=
  Resolved.Query.simple [Resolved.QuerySource.first position] (some (rangeResolved index cell)) [.scalar (.literal (.integer 1))] ["1"]

/-- The resolved SELECT 1 query over fixed ledger metadata rows. -/
def metadataQuery (rows : List (List Value)) (condition : Resolved.Expr) : Resolved.Query :=
  Resolved.Query.simple [Resolved.QuerySource.pragma (pragmaSource pragmaRef (bytes! "ledger") tableInfoNames rows).1]
    (some condition) [.scalar (.literal (.integer 1))] ["1"]

/-- The resolved range, count, account and type subqueries. -/
def guardQueries (position index : Nat) (table : CatalogTable) (cell : CatalogColumn) : List Resolved.Query :=
  [rangeQuery position index cell, Resolved.Query.countOf [Resolved.QuerySource.first position] none "count(*)",
    metadataQuery table.infoRows (nameResolved (bytes! "account")), metadataQuery table.infoRows typedResolved]

/-- One scalar result with the lowest column position it reads. -/
def rangeShape (index : Nat) : SubqueryShape :=
  {parent := none, columns := 1, affinity := none, explicitCollation := none, columnCollation := none, lowest := some index}

/-- The COUNT subquery has one aggregate result and no outer column read. -/
def balanceCountShape : SubqueryShape :=
  {parent := none, columns := 1, affinity := none, explicitCollation := none, columnCollation := none, lowest := none}

/-- The result shapes of the four independent guard subqueries. -/
def guardShapes (index : Nat) : List SubqueryShape := [rangeShape index, balanceCountShape, rangeShape 1, rangeShape 1]

/-- The guard combines an empty bad-range query, a count bound and two metadata witnesses. -/
def guardSyntax : Syntax.Expr := .and (.and (.and (.not (.exists 0))
  (.compare .lt (.subquery 1) (.numeric "1000000"))) (.exists 2)) (.exists 3)

/-- The resolved conjunction preserves the four subquery positions. -/
def guardCondition : Resolved.Expr := .and (.and (.and (.not (.exists 0))
  (.compare .lt none (.subquery 1) (.literal (.integer 1000000)) .binary)) (.exists 2)) (.exists 3)

/-- The guard selects one row only when its conjunction is true. -/
def mainSyntax : Syntax.Subquery :=
  {columns := [.expression (.numeric "1") none "1"], source := none, filter := some guardSyntax,
    joins := [], groupBy := [], orderBy := [], limit := none, offset := none, parent := none}

/-- The result rows of SELECT 1 after applying the given condition. -/
def filteredOnes (context : Resolved.EvalContext) (condition : Resolved.Expr) (rows : List (List Value)) : List (List Value) :=
  (rows.filter (fun row => Resolved.truthy (condition.eval context row))).map (fun _ => [.integer 1])

/-- The corrected SQL guard includes the account column and exact INTEGER declaration. -/
def balanceGuard : Script := sql r"SELECT 1 WHERE
    NOT EXISTS (SELECT 1 FROM ledger WHERE cents NOT BETWEEN -1000000000000 AND 1000000000000)
    AND (SELECT count(*) FROM ledger) < 1000000
    AND EXISTS (SELECT 1 FROM pragma_table_info('ledger') WHERE name = 'account')
    AND EXISTS (SELECT 1 FROM pragma_table_info('ledger') WHERE name = 'cents' AND type = 'INTEGER')"

/-- The account-specific SUM query from the guide. -/
def balance := sql r"SELECT sum(cents) FROM ledger WHERE account = :a"

end BalanceExample
