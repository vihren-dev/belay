import SelectCompoundSupport

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance case A16 of ADR 0027 over every database with the catalog of {lit}`shop`
({lit}`compound_returns`): {lit}`UNION ALL` keeps the rows of both terms with their
multiplicity; {lit}`UNION`, {lit}`INTERSECT` and {lit}`EXCEPT` give each row once, with the members
of their membership rules ({lit}`Resolved.mem_union_combine`, {lit}`Resolved.mem_intersect_combine`,
{lit}`Resolved.mem_except_combine`) when equal rows are the same values. -/

namespace SelectCompoundCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases (cell)
open SelectJoinCases (shop customerRows orderRows shop_found partial_)

/-- A16 with {lit}`UNION ALL`: for every database with the catalog of {name}`shop` and every
environment, the compound returns a result that has each row as often as the {name}`customerIds`
and the {name}`orderCustomerIds` together. Proof sketch: {name}`compound_returns`; {lit}`UNION ALL`
appends the lists, and a permutation keeps the counts. -/
theorem unionAll_counts (script : Script) (one : script.statements.length = 1) (statement : Syntax.Statement)
    (head : script.statements = [(statement, [])])
    (resolves : resolveStatement runContext (shop.raw.connection {}).resolveState statement =
      .ok (.query (compoundQuery .unionAll) terms, (shop.raw.connection {}).resolveState))
    (db : Database) (env : Env) (schema : db.HasCatalog shop) :
    (db.run (query script one) env).returnsResult fun result =>
      ∀ row, result.count row = (customerIds db).count row + (orderCustomerIds db).count row :=
  compound_returns .unionAll script one statement head resolves db env schema rfl _ fun result perm row => by
    simpa [CompoundOperator.combine] using perm.count_eq row

/-- A16 with {lit}`UNION`: for every database with the catalog of {name}`shop` whose ids and
{lit}`customer_id` values that compare equal are the same values ({name}`Resolved.equalRowsIdentical`),
and every environment, the compound returns a result without a duplicate row whose rows are
exactly the rows of the {name}`customerIds` and the {name}`orderCustomerIds`. Proof sketch:
{name}`compound_returns`, {name}`nodup_of_perm` and {name}`Resolved.mem_union_combine`. -/
theorem union_members (script : Script) (one : script.statements.length = 1) (statement : Syntax.Statement)
    (head : script.statements = [(statement, [])])
    (resolves : resolveStatement runContext (shop.raw.connection {}).resolveState statement =
      .ok (.query (compoundQuery .union) terms, (shop.raw.connection {}).resolveState))
    (db : Database) (env : Env) (schema : db.HasCatalog shop)
    (identical : Resolved.equalRowsIdentical [.binary] (customerIds db ++ orderCustomerIds db) = true) :
    (db.run (query script one) env).returnsResult fun result =>
      result.Nodup ∧ ∀ row, row ∈ result ↔ row ∈ customerIds db ∨ row ∈ orderCustomerIds db :=
  compound_returns .union script one statement head resolves db env schema identical _ fun result perm =>
    ⟨nodup_of_perm (by decide) db perm, fun row => perm.mem_iff.trans (Resolved.mem_union_combine identical row)⟩

/-- A16 with {lit}`INTERSECT`: for every database with the catalog of {name}`shop` whose ids that
compare equal are the same values ({name}`Resolved.equalRowsIdentical`), and every environment, the
compound returns a result without a duplicate row whose rows are exactly the {name}`customerIds`
that compare equal to some row of the {name}`orderCustomerIds`. Proof sketch:
{name}`compound_returns`, {name}`nodup_of_perm` and {name}`Resolved.mem_intersect_combine`. -/
theorem intersect_members (script : Script) (one : script.statements.length = 1) (statement : Syntax.Statement)
    (head : script.statements = [(statement, [])])
    (resolves : resolveStatement runContext (shop.raw.connection {}).resolveState statement =
      .ok (.query (compoundQuery .intersect) terms, (shop.raw.connection {}).resolveState))
    (db : Database) (env : Env) (schema : db.HasCatalog shop)
    (identical : Resolved.equalRowsIdentical [.binary] (customerIds db) = true) :
    (db.run (query script one) env).returnsResult fun result =>
      result.Nodup ∧ ∀ row, row ∈ result ↔
        row ∈ customerIds db ∧ (orderCustomerIds db).any (Resolved.sameOutput [.binary] row) = true :=
  compound_returns .intersect script one statement head resolves db env schema identical _ fun result perm =>
    ⟨nodup_of_perm (by decide) db perm,
      fun row => perm.mem_iff.trans (Resolved.mem_intersect_combine identical _ row)⟩

/-- A16 with {lit}`EXCEPT`: for every database with the catalog of {name}`shop` whose ids that
compare equal are the same values ({name}`Resolved.equalRowsIdentical`), and every environment, the
compound returns a result without a duplicate row whose rows are exactly the {name}`customerIds`
that compare equal to no row of the {name}`orderCustomerIds`. Proof sketch:
{name}`compound_returns`, {name}`nodup_of_perm` and {name}`Resolved.mem_except_combine`. -/
theorem except_members (script : Script) (one : script.statements.length = 1) (statement : Syntax.Statement)
    (head : script.statements = [(statement, [])])
    (resolves : resolveStatement runContext (shop.raw.connection {}).resolveState statement =
      .ok (.query (compoundQuery .except) terms, (shop.raw.connection {}).resolveState))
    (db : Database) (env : Env) (schema : db.HasCatalog shop)
    (identical : Resolved.equalRowsIdentical [.binary] (customerIds db) = true) :
    (db.run (query script one) env).returnsResult fun result =>
      result.Nodup ∧ ∀ row, row ∈ result ↔
        row ∈ customerIds db ∧ (orderCustomerIds db).any (Resolved.sameOutput [.binary] row) = false :=
  compound_returns .except script one statement head resolves db env schema identical _ fun result perm =>
    ⟨nodup_of_perm (by decide) db perm,
      fun row => perm.mem_iff.trans (Resolved.mem_except_combine identical _ row)⟩

/-- The A16 script of {lit}`UNION ALL`, which keeps the rows of both terms with their multiplicity. -/
def unionAllScript : Script := sql r"SELECT c.id FROM customers c UNION ALL SELECT o.customer_id FROM orders o"
/-- The A16 script of {lit}`UNION`, which keeps each row of either term once. -/
def unionScript : Script := sql r"SELECT c.id FROM customers c UNION SELECT o.customer_id FROM orders o"
/-- The A16 script of {lit}`INTERSECT`, which keeps each row of the left term that the right term has, once. -/
def intersectScript : Script := sql r"SELECT c.id FROM customers c INTERSECT SELECT o.customer_id FROM orders o"
/-- The A16 script of {lit}`EXCEPT`, which keeps each row of the left term that the right term does not have, once. -/
def exceptScript : Script := sql r"SELECT c.id FROM customers c EXCEPT SELECT o.customer_id FROM orders o"

/-- The scripts resolve to {name}`compoundQuery` with its {name}`terms` on {name}`shop`. -/
example : resolveStatement runContext (shop.raw.connection {}).resolveState (unionAllScript.statements[0]'(by decide)).1 =
      .ok (.query (compoundQuery .unionAll) terms, (shop.raw.connection {}).resolveState) ∧
    resolveStatement runContext (shop.raw.connection {}).resolveState (exceptScript.statements[0]'(by decide)).1 =
      .ok (.query (compoundQuery .except) terms, (shop.raw.connection {}).resolveState) := by
  decide +kernel

/-- A16 contrast: on {name}`partial_`, {lit}`UNION ALL` keeps the id 1 of {lit}`acme` twice, once
from each term, where {lit}`UNION` keeps it once; {lit}`INTERSECT` keeps 1 and {lit}`EXCEPT` keeps 2.
Native SQLite 3.51.0 gives the same rows. -/
example : (partial_.run (query unionAllScript rfl)).returnsResult
      (·.Perm [[.integer 1], [.integer 2], [.integer 1], [.integer 9], [.null]]) ∧
    (partial_.run (query unionScript rfl)).returnsResult (·.Perm [[.null], [.integer 1], [.integer 2], [.integer 9]]) ∧
    (partial_.run (query intersectScript rfl)).returnsResult (· = [[.integer 1]]) ∧
    (partial_.run (query exceptScript rfl)).returnsResult (· = [[.integer 2]]) := by
  decide +kernel

#print axioms unionAll_counts
#print axioms union_members
#print axioms intersect_members
#print axioms except_members

end SelectCompoundCases
