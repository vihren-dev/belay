import Belay

/-! GROUP BY's no-duplicate condition is sufficient for a column key. NULL and non-ASCII
case pairs exercise the exact boundary of the implication and of NOCASE. -/

open Belay.Sqlite.Model

/-- The key used by the guide's unique email index. -/
def emailKey : UniqueKey := { terms := [{ term := .column 0, collation := .nocase }] }

/-- A table with one email column, with rowids deliberately out of insertion order. -/
def emails (first second : Value) : Table :=
  { shape := { columns := [{ name := name! "email", declaredType := none }] },
    rows := [⟨2, [first]⟩, ⟨1, [second]⟩] }

/-- No group has a repeated email under the index collation. -/
abbrev distinctGroups (table : Table) : Prop :=
  ∀ group ∈ Resolved.groups (.plain 0) [(.column 0, .nocase)] (Resolved.sourceRows table),
    group.length ≤ 1

/-- For every table, the grouping claim guarantees absence of a key conflict, independent
of scan order. Proof sketch: apply the column-group bridge to the only key term. -/
theorem groups_imply_unique (table : Table) (distinct : distinctGroups table) :
    LiteralData.uniqueRows emailKey table.rows = true :=
  LiteralData.uniqueRows_of_column_groups table (.plain 0) (by simp [emailKey]) distinct

example : distinctGroups (emails (.text "a@x".toUTF8.toList) (.text "b@x".toUTF8.toList)) := by decide +kernel
example : LiteralData.uniqueRows emailKey
    (emails (.text "a@x".toUTF8.toList) (.text "b@x".toUTF8.toList)).rows = true :=
  groups_imply_unique _ (by decide +kernel)

example : ¬ distinctGroups (emails (.text "a@x".toUTF8.toList) (.text "A@X".toUTF8.toList)) ∧
    LiteralData.uniqueRows emailKey (emails (.text "a@x".toUTF8.toList) (.text "A@X".toUTF8.toList)).rows = false := by
  decide +kernel

-- NULLs group together but never conflict on the key: the converse would be false.
example : ¬ distinctGroups (emails .null .null) ∧
    LiteralData.uniqueRows emailKey (emails .null .null).rows = true := by decide +kernel

-- NOCASE folds only ASCII. These two addresses pass both the grouping and the key check.
example : distinctGroups (emails (.text "é@x".toUTF8.toList) (.text "É@x".toUTF8.toList)) ∧
    LiteralData.uniqueRows emailKey (emails (.text "é@x".toUTF8.toList) (.text "É@x".toUTF8.toList)).rows = true := by
  decide +kernel

#print axioms groups_imply_unique
