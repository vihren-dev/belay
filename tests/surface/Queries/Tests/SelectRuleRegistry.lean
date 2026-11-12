import SelectOrderCases

set_option doc.verso true

/-! A fixture module of {lit}`tests/surface_select_rules_test.py`: the registry of the attribute
{lit}`sql_select_rule`. The attribute refuses a declaration that is no theorem, a phase name that it does
not know and a scoped registration. A local registration ends with its section. The procedure tries the
registered rules of a phase in qualified declaration-name order, not in the order of registration, and a
rule that the procedure cannot use leaves the goal and its explanation. A proof without the attribute
applies the same rule by hand. -/

namespace SelectRuleRegistry
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases

/-- A row is wide when it has at least three cells. The built-in rules do not know this predicate, and
the procedure does not unfold a structure, so a proof of it needs a rule of the user. -/
structure Wide (row : List Value) : Prop where
  /-- The row has at least three cells. -/
  long : 3 ≤ row.length

/-- Source rule of the user: for every database with the catalog of {name}`orders`, each scanned row of
its first table is {name}`Wide`. Proof sketch: the built-in source rule {name}`Database.mem_scanAt`
gives the length of the row, which is the three columns of the table. -/
theorem wide_of_scan {db : Database} (schema : db.HasCatalog orders) {row : List Value}
    (member : row ∈ db.scanAt 0) : Wide row := by
  have ⟨length, _⟩ := Database.mem_scanAt (shape := ordersShape) schema (by decide +kernel) member
  exact ⟨by rw [length]; decide +kernel⟩

/-- A value that is no theorem. -/
def notATheorem : Nat := 1

/-- error: sql_select_rule: `SelectRuleRegistry.notATheorem` is not a theorem. Register a proved theorem. -/
#guard_msgs in
attribute [sql_select_rule source] notATheorem

/-- error: sql_select_rule: unknown phase `sorting`. Use one of: source, expression, filter, group, aggregate, having, project, distinct, order, window, compound, subquery, execution. -/
#guard_msgs in
attribute [sql_select_rule sorting] wide_of_scan

/-- error: sql_select_rule: scoped registration is not supported. Use a global or a local registration. -/
#guard_msgs in
attribute [scoped sql_select_rule source] wide_of_scan

section
attribute [local sql_select_rule source] wide_of_scan

/-- For every database with the catalog of {name}`orders`, each scanned row of its first table is
{name}`Wide`. The local registration of {name}`wide_of_scan` closes the goal. -/
theorem wide_inside (db : Database) (schema : db.HasCatalog orders) (row : List Value)
    (member : row ∈ db.scanAt 0) : Wide row := by
  sql_select [schema]

end

#guard_msgs (drop warning) in
/-- The claim of {name}`wide_inside` after its section. The registration has ended, so the procedure
stops with a warning and leaves the goal; the proof then applies the rule by hand, without the
attribute. The manual step fails if the procedure closes the goal. -/
theorem wide_after (db : Database) (schema : db.HasCatalog orders) (row : List Value)
    (member : row ∈ db.scanAt 0) : Wide row := by
  sql_select [schema]
  exact wide_of_scan schema member

/-- Execution rule that never applies: its premise is false. -/
theorem _root_.Zz.blocked_last {db : Database} {script : Script} {one : script.statements.length = 1} {env : Env}
    {property : List (List Value) → Prop} (blocked : 1 = 2) (_each : ∀ result, property result) :
    (db.run (query script one) env).returnsResult property := absurd blocked (by decide)

/-- Execution rule that never applies: its premise is false. -/
theorem _root_.Aa.blocked_first {db : Database} {script : Script} {one : script.statements.length = 1} {env : Env}
    {property : List (List Value) → Prop} (blocked : 2 = 3) (_each : ∀ result, property result) :
    (db.run (query script one) env).returnsResult property := absurd blocked (by decide)

attribute [sql_select_rule execution] Zz.blocked_last
attribute [sql_select_rule execution] Aa.blocked_first

/-- warning: sql_select stopped in the execution phase: the rule Aa.blocked_first matches, but its premise
  2 = 3
is not proved. The goal stays open:
  db : Database
  env : Env
  ⊢ (db.run (query SelectOrderCases.idsDescending SelectOrderCases.idsDescending_one) env).returnsResult fun x => True
---
warning: declaration uses `sorry` -/
#guard_msgs in
/-- Without the catalog fact, no execution rule applies. The explanation names the first rule in
qualified declaration-name order, {name}`Aa.blocked_first`, though {name}`Zz.blocked_last` was
registered first. -/
example (db : Database) (env : Env) :
    (db.run (query SelectOrderCases.idsDescending SelectOrderCases.idsDescending_one) env).returnsResult
      fun _ => True := by
  sql_select
  sorry

#print axioms wide_of_scan
#print axioms wide_inside
#print axioms wide_after

end SelectRuleRegistry
