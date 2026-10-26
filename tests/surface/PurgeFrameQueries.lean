import Belay

/-! A fixture module of `tests/surface_assertion_examples_test.py`: the purge of the guide and its frame claim
(ADR 0017, S6). The purge deletes the expired sessions of one customer. The claim reads the start through the
schema `before`: every session that is not an expired session of the customer is still there. This module gives the
two scripts, the resolved forms that the claim needs, and the conditions under which the model resolves and runs them
as the claim says ({name}`PurgeFrameSite`). The final property of the claim is not a field of the site. -/

set_option doc.verso true

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- The purge of the guide: the expired sessions of one customer. Each named parameter becomes an argument. -/
def purge := sql r"DELETE FROM sessions WHERE customer_id = :c AND expires_at < :now"

/-- The frame claim of the guide: no session that the purge is not meant to delete is missing. A session that is
not an expired session of the customer is a row of {lit}`before.sessions` for which the condition is not 1, also when
a parameter is NULL. -/
def purgeKeeps (c now : Value) : Script :=
  sql r"SELECT 1 WHERE NOT EXISTS (SELECT * FROM before.sessions WHERE (customer_id = $c AND expires_at < $now) IS NOT 1 EXCEPT SELECT * FROM sessions)"

/-- The syntax tree of the purge, which does not depend on the two values. -/
def purgeStatement : Syntax.Statement := ((purge .null .null).statements.headD (.begin, [])).1

/-- The syntax tree of the frame claim, which does not depend on the two values. -/
def purgeKeepsStatement : Syntax.Statement := ((purgeKeeps .null .null).statements.headD (.begin, [])).1

/-- For every pair of values, the script of the purge is its statement with the two values. -/
theorem purge_script (c now : Value) : purge c now = ⟨[(purgeStatement, [c, now])]⟩ := rfl

/-- For every pair of values, the script of the claim is its statement with the two values. -/
theorem purgeKeeps_script (c now : Value) : purgeKeeps c now = ⟨[(purgeKeepsStatement, [c, now])]⟩ := rfl

/-- The filter of the purge as the model resolves it: the customer id is the first parameter and the expiry time is
less than the second, both compared with INTEGER affinity. -/
def purgeFilter : Resolved.Expr :=
  .and (.compare .eq (some .integer) (.column 1) (.parameter 1) .binary)
    (.compare .lt (some .integer) (.column 2) (.parameter 2) .binary)

/-- The condition of the claim as the model resolves it: the filter of the purge {lit}`IS NOT 1`. -/
def purgeKeepsCondition : Resolved.Expr := .compare .isNot none purgeFilter (.literal (.integer 1)) .binary

/-- The columns of {lit}`SELECT *` over the three columns of {lit}`sessions`. -/
def sessionColumns : List Resolved.Expr := [.column 0, .column 1, .column 2]

/-- The compound {lit}`q1 EXCEPT q2` of the claim as the model resolves it, under the names of the columns. -/
def purgeKeepsCompound (names : List String) : Resolved.Query :=
  { Resolved.Query.simple [] none [] names with
    compound := some { first := 1, rest := [(.except, 2)], collations := [.binary, .binary, .binary] } }

/-- The statement of the claim as the model resolves it, for the table at a position: it checks that no row of the
table of the initial database with the condition is missing from the table of the current database. -/
def purgeKeepsResolved (position : Nat) (names : List String) : Resolved.Statement :=
  Resolved.notExistsExcept (purgeKeepsCompound names) position purgeKeepsCondition sessionColumns names

/-- The filter of the purge reads only its row and the two values. -/
theorem purgeFilter_rowwise : purgeFilter.Rowwise :=
  .and (.compare _ _ _ (.column 1) (.parameter 1)) (.compare _ _ _ (.column 2) (.parameter 2))

/-- The condition of the claim reads only its row and the two values. -/
theorem purgeKeepsCondition_rowwise : purgeKeepsCondition.Rowwise :=
  .compare _ _ _ purgeFilter_rowwise (.literal _)

/-- Every column of {lit}`SELECT *` over {lit}`sessions` reads only its row. -/
theorem sessionColumns_rowwise : ∀ c ∈ sessionColumns, c.Rowwise := by
  intro c member
  simp only [sessionColumns, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl <;> exact .column _

/-- For every names, the compound has the shape that the model laws describe: no source and no expression of its
own, no window, and the compound of the terms 1 and 2 under the binary collation. -/
theorem purgeKeepsCompound_shape (names : List String) :
    (purgeKeepsCompound names).PlainExcept 1 2 [.binary, .binary, .binary] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The query and the subqueries of the syntax tree of the claim, as the two-state observation reads them. -/
def purgeKeepsParts : Syntax.Subquery × List Syntax.Subquery := purgeKeepsStatement.asQuery?.get (by decide +kernel)

/-- The syntax tree of the claim is a {lit}`SELECT` with these parts. -/
theorem purgeKeepsStatement_asQuery : purgeKeepsStatement.asQuery? = some purgeKeepsParts := by
  simp [purgeKeepsParts]

/-- The claim names the schema {lit}`before`, so the observation reads the initial database. -/
theorem purgeKeeps_usesSchema : usesSchema purgeKeepsParts.1 purgeKeepsParts.2 = true := by decide +kernel

#print axioms purgeFilter_rowwise
#print axioms purgeKeepsCondition_rowwise
#print axioms sessionColumns_rowwise
#print axioms purgeKeepsCompound_shape

end AssertionExamples
