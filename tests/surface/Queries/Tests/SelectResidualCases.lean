import SelectProcedureCases

set_option doc.verso true

/-! A fixture module of {lit}`tests/surface_select_rules_test.py`: the goals that {lit}`sql_select` leaves
and their explanations (B04, B09). Each kind of stop has its own explanation: a goal of an unknown shape
is refused with an error; a premise of the execution rule that the procedure cannot prove stops it in the
execution phase; a claim that the facts of the rules do not prove stops it in the result phase, with the
claim of the user as the goal; and rules or hints without end stop it at its limit of rule applications.
Each residual goal of a theorem is then proved by hand, which shows that it is the goal that is left; the
case of the execution rule checks only the explanation. A premise that the procedure cannot prove comes
before the end of its fuel: when both occur, the explanation names the premise. -/

namespace SelectResidualCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases

/-- error: sql_select proves a claim about the results of a query: returnsResult or returnsRows of a run, the check of a query (Sql.check), or a goal whose target or hypotheses read the results or a phase of a resolved query (Resolved) or the rows of a table (Database.scanAt). This goal is none of these, and no hint applies to it. Use another tactic, or pass a rule as a hint. -/
#guard_msgs in
/-- A plain fact is no claim about a query: the procedure refuses it. -/
example : (2 : Nat) + 2 = 4 := by
  sql_select

/-- A query with a subquery in its filter. The built-in rules have no subquery rule, so the execution rule
requires a query without subqueries. -/
def withSubquery : Script := sql r"SELECT customer FROM orders WHERE id IN (SELECT id FROM orders)"

/-- The script {name}`withSubquery` has one statement. -/
theorem withSubquery_one : withSubquery.statements.length = 1 := rfl

/-- warning: sql_select stopped in the execution phase: the rule Belay.Sqlite.Run.query_returnsResult_ofCatalog matches, but its premise
  orders.selectQuery? -/
#guard_msgs (warning, substring := true) in
/-- A claim outside the rules: the execution rule matches, but its premise that the query resolves to a
query without subqueries ({name}`Database.selectQuery?`) is not proved. The procedure stops in the
execution phase and shows the premise; the claim of the user is not the cause. -/
example (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    (db.run (query withSubquery withSubquery_one) env).returnsResult fun _ => True := by
  sql_select [schema]
  sorry

/-- warning: sql_select stopped in the result phase: the facts that the rules give do not prove the goal. Prove it, or pass a rule or a fact as a hint. The goal stays open:
  case each
  db : Database
  env : Env
  schema : db.HasCatalog orders -/
#guard_msgs (warning, substring := true) in
/-- Arithmetic of the user that the evaluation laws do not prove: for every database with the catalog of
{name}`orders` and every environment, {lit}`count(*)` returns one row with the square of the number of
scanned rows divided by that number. The procedure stops in the result phase. The goal that stays is
the claim of the user about the result, under the facts of the rules: with the fact of the aggregate
rule and the evaluation laws, it is the arithmetic alone, which the proof then gives. -/
theorem count_arithmetic (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    (db.run (query SelectCountCases.countAll SelectCountCases.countAll_one) env).returnsResult
      (· = [[.integer ((db.scanAt 0).length ^ 2 / (db.scanAt 0).length)]]) := by
  sql_select [schema]
  show List.map Prod.fst _ = [[Value.integer ((db.scanAt 0).length ^ 2 / (db.scanAt 0).length)]]
  rename_i fact _ _ _
  rw [fact]
  simp [sql_select_simp]
  show ((db.scanAt 0).length : Int) = ((db.scanAt 0).length : Int) ^ 2 / ((db.scanAt 0).length : Int)
  generalize (db.scanAt 0).length = count
  rcases count with _ | count
  · rfl
  · rw [Int.pow_succ, Int.pow_one, Int.mul_ediv_cancel _ (by omega)]

/-- A row is red. The built-in rules do not know this predicate. -/
structure Red (row : List Value) : Prop where
  /-- Every row can be red. -/
  red : True

/-- A row is blue. The built-in rules do not know this predicate. -/
structure Blue (row : List Value) : Prop where
  /-- Every row can be blue. -/
  blue : True

/-- A row is green. No rule gives this predicate. -/
structure Green (row : List Value) : Prop where
  /-- Every row can be green. -/
  green : True

/-- A row is deep to a depth. -/
structure Deep (row : List Value) (depth : Nat) : Prop where
  /-- Every row can be deep. -/
  deep : True

/-- For every row: a red row is blue. -/
theorem blue_of_red {row : List Value} (_ : Red row) : Blue row := ⟨trivial⟩

/-- For every row: a blue row is red. With {name}`blue_of_red`, the rules make a cycle. -/
theorem red_of_blue {row : List Value} (_ : Blue row) : Red row := ⟨trivial⟩

/-- For every row and depth: a row that is deep to the depth is deep to the next depth. Applied forward,
the rule gives a new fact each time, without end. -/
theorem deeper {row : List Value} {depth : Nat} (_ : Deep row depth) : Deep row (depth + 1) := ⟨trivial⟩

/-- For every row: a blue row is green, if 1 is 2. The premise is false, so the rule never applies. -/
theorem green_of_blue {row : List Value} (_ : 1 = 2) (_ : Blue row) : Green row := ⟨trivial⟩

section
attribute [local sql_select_rule filter] blue_of_red red_of_blue

/-- For every database, scanned row of its first table that is red: the row is blue. The cyclic rules
{name}`blue_of_red` and {name}`red_of_blue` close the goal; each applies once to a fact. -/
theorem blue_by_cycle (db : Database) (row : List Value) (_member : row ∈ db.scanAt 0) (red : Red row) :
    Blue row := by
  sql_select

/-- warning: sql_select stopped in the result phase: the facts that the rules give do not prove the goal. Prove it, or pass a rule or a fact as a hint. The goal stays open:
  db : Database
  row : List Value
  _member : row ∈ db.scanAt 0
  _red : Red row
  fact : Blue row
  ⊢ Green row -/
#guard_msgs in
/-- No rule gives {name}`Green`. The cyclic rules end after one step each, and the goal stays with the fact
that they give. -/
theorem green_after_cycle (db : Database) (row : List Value) (_member : row ∈ db.scanAt 0) (_red : Red row) :
    Green row := by
  sql_select
  exact ⟨trivial⟩

end

section
attribute [local sql_select_rule filter] deeper

/-- warning: sql_select stopped in the result phase: the procedure used its limit of 64 rule applications. Rules or hints that make new goals or facts without end use this limit. This does not show that the goal is false. Pass fewer hints, or prove the goal in steps. The goal stays open:
  db : Database
  row : List Value
  _member : row ∈ db.scanAt 0
  _deep : Deep row 0
  fact✝⁶² : Deep row (0 + 1) -/
#guard_msgs (warning, substring := true) in
/-- The rule {name}`deeper` gives a new fact at each step. The procedure stops at its limit of rule
applications, with an explanation that differs from that of a claim that the facts do not prove. -/
theorem green_after_limit (db : Database) (row : List Value) (_member : row ∈ db.scanAt 0) (_deep : Deep row 0) :
    Green row := by
  sql_select
  exact ⟨trivial⟩

end

/-- warning: sql_select stopped in the result phase: the procedure used its limit of 64 rule applications. Rules or hints that make new goals or facts without end use this limit. This does not show that the goal is false. Pass fewer hints, or prove the goal in steps. The goal stays open:
  case x
  db : Database
  row : List Value
  _member : row ∈ db.scanAt 0
  ⊢ Blue row -/
#guard_msgs in
/-- Two hints that apply backward to each other's premise. The procedure stops at its limit of rule
applications and leaves the goal of the cycle. -/
theorem blue_after_hint_cycle (db : Database) (row : List Value) (_member : row ∈ db.scanAt 0) : Blue row := by
  sql_select [blue_of_red, red_of_blue]
  exact ⟨trivial⟩

/-- warning: sql_select stopped in the result phase: the rule green_of_blue matches, but its premise
  1 = 2
is not proved. The goal stays open:
  db : Database
  row : List Value
  _member : row ∈ db.scanAt 0
  ⊢ Green row -/
#guard_msgs in
/-- A hint keeps its premises: the conclusion of {name}`green_of_blue` matches the goal, but its premise
{lit}`1 = 2` is not proved, so the hint does not apply, and the explanation names the hint and the
premise. -/
theorem green_with_false_premise (db : Database) (row : List Value) (_member : row ∈ db.scanAt 0) :
    Green row := by
  sql_select [green_of_blue]
  exact ⟨trivial⟩

end SelectResidualCases

#print axioms SelectResidualCases.count_arithmetic
#print axioms SelectResidualCases.blue_by_cycle
#print axioms SelectResidualCases.green_after_cycle
#print axioms SelectResidualCases.green_after_limit
#print axioms SelectResidualCases.blue_after_hint_cycle
#print axioms SelectResidualCases.green_with_false_premise
