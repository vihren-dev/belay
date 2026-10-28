import Belay.Sqlite.Model.Comparison

set_option doc.verso true

/-! Laws relating BINARY value equality to the built-in collations. -/

namespace Belay.Sqlite.Model

/-- For every pair of values equal under BINARY comparison, every built-in collation
also compares them as equal. Proof sketch: equal ranks and byte strings settle text;
the other storage classes retain the BINARY comparison. -/
theorem Collation.compare_eq_of_binary {first second : Value} (equal : Value.compare first second = .eq)
    (collation : Collation) : collation.compare first second = .eq := by
  have parts := equal
  simp only [Value.compare, compareLex_eq_eq, compareOn] at parts
  have ranks : first.rank = second.rank := Std.LawfulEqCmp.eq_of_compare parts.1
  have bytes : first.bytes = second.bytes := Std.LawfulEqCmp.eq_of_compare parts.2.2
  cases first <;> cases second <;> cases collation <;>
    simp only [Collation.compare, Collation.key] <;> try exact equal
  all_goals simp_all [Value.rank, Value.bytes]
  all_goals first
    | exact Std.ReflCmp.compare_self (cmp := Value.compare)
    | have impossible := parts.1
      split at impossible <;> contradiction

end Belay.Sqlite.Model
