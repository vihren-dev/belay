import Belay.Sqlite.Model.Queries.Evaluation.QueryLaws
import Belay.Sqlite.Model.Queries.Evaluation.SumValueLaws

set_option doc.verso true

/-! The value rules of the aggregates (ADR 0027, D1, phase {lit}`aggregate`): what
{name}`Belay.Sqlite.Model.Resolved.Aggregate.eval` gives over the rows of a group. An aggregate of an
operand that is NULL on every row, which includes a group of no row, gives NULL for {lit}`sum`,
{lit}`avg`, {lit}`min`, {lit}`max` and {lit}`group_concat`, 0 for {lit}`count` and 0.0 for
{lit}`total`. {lit}`count(x)` is {lit}`count(*)` when {lit}`x` is never NULL. {lit}`min` and
{lit}`max` give a value of the operand that no other value is less (more) than under the
collation: the modeled comparison, not a numeric order. {lit}`group_concat` without a separator
joins the texts of its values with commas. -/

namespace Belay.Sqlite.Model.Resolved

/-- For every value, the value is NULL when {name}`Value.isNull` is true. Proof sketch: by cases on
the value; {name}`Value.isNull` is false for every value that is not NULL. -/
theorem Value.eq_null_of_isNull {value : Value} (null : value.isNull = true) : value = .null := by
  cases value <;> simp_all [Value.isNull]

/-- For every list of NULL values, the state of {lit}`SUM` after the list is the empty state:
{lit}`SUM` skips NULL. Proof sketch: induction; a NULL value has no sum input. -/
theorem sumOf_allNull : ∀ {values : List Value}, (∀ value ∈ values, value.isNull = true) → sumOf values = {}
  | [], _ => rfl
  | value :: rest, nulls => by
    have head := Value.eq_null_of_isNull (nulls value (List.mem_cons_self ..))
    subst head
    exact sumOf_allNull (values := rest) fun other member => nulls other (List.mem_cons_of_mem _ member)

/-- All-NULL rule: for every context, rows and operand that is NULL on every row (for example over
no row), {lit}`count(x)` is 0; {lit}`sum`, {lit}`avg`, {lit}`min`, {lit}`max` and
{lit}`group_concat` without a separator are NULL; {lit}`total` is 0.0; and {lit}`sum` does not
fail. Proof sketch: the state of {lit}`SUM` is the empty state ({name}`sumOf_allNull`), the
extremum and the text of no value that is not NULL are NULL, and no row is counted. -/
theorem Aggregate.eval_allNull (context : EvalContext) (rows : List (List Value)) (operand : Expr)
    (collation : Collation) (nulls : ∀ row ∈ rows, (operand.eval context row).isNull = true) :
    (Aggregate.count operand).eval context rows = .integer 0 ∧
      (Aggregate.sum operand).eval context rows = .null ∧ (Aggregate.sum operand).fails context rows = false ∧
      (Aggregate.avg operand).eval context rows = .null ∧
      (Aggregate.total operand).eval context rows = realValue (Float.ofInt 0) ∧
      (Aggregate.min operand collation).eval context rows = .null ∧
      (Aggregate.max operand collation).eval context rows = .null ∧
      (Aggregate.groupConcat operand none).eval context rows = .null := by
  have values : ∀ value ∈ rows.map (operand.eval context), value.isNull = true := by
    simpa using nulls
  have noValue : (rows.map (operand.eval context)).filter (!·.isNull) = [] :=
    List.filter_eq_nil_iff.mpr fun value member => by simp [values value member]
  have concat : ∀ (text : Option (List UInt8)) (items : List (List Value)), (∀ row ∈ items,
      (operand.eval context row).isNull = true) →
      concatRows text (items.map fun row => (operand.eval context row, none)) = text := by
    intro text items
    induction items with
    | nil => intro _; rfl
    | cons row rest ih =>
      intro allNull
      simp only [List.map_cons, concatRows, allNull row (List.mem_cons_self ..), ite_true]
      exact ih fun other member => allNull other (List.mem_cons_of_mem _ member)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Aggregate.eval] using nulls
  · simp [Aggregate.eval, sumOf_allNull values, SumState.sumValue]
  · simp [Aggregate.fails, sumOf_allNull values, SumState.sumValue]
  · simp [Aggregate.eval, sumOf_allNull values, SumState.averageValue]
  · simp [Aggregate.eval, sumOf_allNull values, SumState.totalValue]
  · simp [Aggregate.eval, extremum, noValue]
  · simp [Aggregate.eval, extremum, noValue]
  · simp [Aggregate.eval, groupConcatValue, concat none rows nulls]

/-- Non-NULL count rule: for every context, rows and operand that is not NULL on any row,
{lit}`count(x)` is {lit}`count(*)`: the number of rows. Proof sketch: the filter of the counted
rows keeps every row. -/
theorem Aggregate.eval_count_of_notNull (context : EvalContext) (rows : List (List Value)) (operand : Expr)
    (present : ∀ row ∈ rows, (operand.eval context row).isNull = false) :
    (Aggregate.count operand).eval context rows = Aggregate.countRows.eval context rows := by
  have keep : rows.filter (fun row => !(operand.eval context row).isNull) = rows :=
    List.filter_eq_self.mpr fun row member => by simp [present row member]
  simp only [Aggregate.eval, keep]

/-- One step of the extremum fold keeps its invariant: for every comparison that is a total order,
value that is not NULL, previous best and seen values, if the best is NULL with nothing seen, or a
seen value that is not NULL and at most every seen value, then after the step the same holds with
the value seen too. Proof sketch: by cases on the invariant and on the comparison of the value
with the best; the order is transitive, and its opposite is the swapped comparison. -/
theorem extremum_step {cmp : Value → Value → Ordering} [Std.TransCmp cmp] {value best : Value}
    {seen : List Value} (present : value.isNull = false)
    (invariant : (best.isNull = true ∧ seen = []) ∨ (best ∈ seen ∧ best.isNull = false ∧ ∀ u ∈ seen, (cmp best u).isLE)) :
    let next := if best.isNull || (cmp value best == .lt) then value else best
    next ∈ seen ++ [value] ∧ next.isNull = false ∧ ∀ u ∈ seen ++ [value], (cmp next u).isLE := by
  intro next
  rcases invariant with ⟨null, rfl⟩ | ⟨member, notNull, least⟩
  · have chosen : next = value := by simp [next, null]
    rw [chosen]
    refine ⟨by simp, present, fun u inU => ?_⟩
    have single : u = value := by simpa using inU
    rw [single]
    exact Std.ReflCmp.isLE_rfl
  · by_cases less : cmp value best = .lt
    · have chosen : next = value := by simp [next, less]
      rw [chosen]
      refine ⟨by simp, present, fun u inU => ?_⟩
      rcases List.mem_append.mp inU with old | new
      · exact Std.TransCmp.isLE_trans (by simp [less]) (least u old)
      · rw [List.mem_singleton.mp new]
        exact Std.ReflCmp.isLE_rfl
    · have chosen : next = best := by simp [next, notNull, less]
      rw [chosen]
      refine ⟨List.mem_append_left _ member, notNull, fun u inU => ?_⟩
      rcases List.mem_append.mp inU with old | new
      · exact least u old
      · rw [List.mem_singleton.mp new, Std.OrientedCmp.eq_swap (cmp := cmp) (a := best) (b := value)]
        cases order : cmp value best <;> simp [order, Ordering.swap] at less ⊢

/-- Extremum rule: for every comparison that is a total order and values, the extremum of the
values that are less ({name}`extremum` with the test {lit}`cmp a b == .lt`) is NULL exactly when
every value is NULL; otherwise it is one of the values, it is not NULL, and it is at most every value
that is not NULL. Proof sketch: induction on the values that are not NULL, with the invariant of
{name}`extremum_step`. -/
theorem extremum_spec {cmp : Value → Value → Ordering} [Std.TransCmp cmp] (values : List Value) :
    ((extremum (fun a b => cmp a b == .lt) values).isNull = true ↔ ∀ value ∈ values, value.isNull = true) ∧
      ((extremum (fun a b => cmp a b == .lt) values).isNull = false →
        extremum (fun a b => cmp a b == .lt) values ∈ values ∧
          ∀ value ∈ values, value.isNull = false → (cmp (extremum (fun a b => cmp a b == .lt) values) value).isLE) := by
  have fold : ∀ (items seen : List Value) (best : Value), (∀ v ∈ items, v.isNull = false) →
      ((best.isNull = true ∧ seen = []) ∨ (best ∈ seen ∧ best.isNull = false ∧ ∀ u ∈ seen, (cmp best u).isLE)) →
      let result := items.foldl (fun best value => if best.isNull || (cmp value best == .lt) then value else best) best
      (result.isNull = true ∧ seen ++ items = []) ∨
        (result ∈ seen ++ items ∧ result.isNull = false ∧ ∀ u ∈ seen ++ items, (cmp result u).isLE) := by
    intro items
    induction items with
    | nil => intro seen best _ invariant; simpa using invariant
    | cons value rest ih =>
      intro seen best present invariant
      have step := extremum_step (cmp := cmp) (present value (List.mem_cons_self ..)) invariant
      simpa using ih (seen ++ [value]) _ (fun v member => present v (List.mem_cons_of_mem _ member))
        (.inr step)
  have result := fold (values.filter (!·.isNull)) [] .null (by simp) (.inl ⟨rfl, rfl⟩)
  simp only [List.nil_append] at result
  have same : extremum (fun a b => cmp a b == .lt) values = (values.filter (!·.isNull)).foldl
      (fun best value => if best.isNull || (cmp value best == .lt) then value else best) .null := rfl
  rw [same]
  revert result
  generalize (values.filter (!·.isNull)).foldl
    (fun best value => if best.isNull || (cmp value best == .lt) then value else best) Value.null = best
  rintro (⟨null, empty⟩ | ⟨member, notNull, least⟩)
  · rw [List.filter_eq_nil_iff] at empty
    exact ⟨⟨fun _ value inValues => by simpa using empty value inValues, fun _ => null⟩, by simp [null]⟩
  · refine ⟨⟨by simp [notNull], fun allNull => ?_⟩, fun _ => ⟨(List.mem_filter.mp member).1, fun value inValues
      present => least value (List.mem_filter.mpr ⟨inValues, by simp [present]⟩)⟩⟩
    obtain ⟨inValues, keep⟩ := List.mem_filter.mp member
    simp [allNull _ inValues] at keep

/-- {lit}`group_concat` rule: for every context, operand and group of a first row and later rows on
which the operand is not NULL, {lit}`group_concat` without a separator is the TEXT of the first row's
value ({name}`concatText`) followed, for each later row in order, by a comma (byte 44) and the row's
value. For example the values {lit}`'a'` and {lit}`'b'` give {lit}`'a,b'`. Proof sketch: induction on
the later rows with the text so far; each row that is not NULL adds the comma and its text. -/
theorem Aggregate.eval_groupConcat_of_notNull (context : EvalContext) (operand : Expr) (first : List Value)
    (rest : List (List Value)) (present : ∀ row ∈ first :: rest, (operand.eval context row).isNull = false) :
    (Aggregate.groupConcat operand none).eval context (first :: rest) =
      .text (concatText (operand.eval context first) ++
        (rest.map fun row => 44 :: concatText (operand.eval context row)).flatten) := by
  have joined : ∀ (text : List UInt8) (items : List (List Value)),
      (∀ row ∈ items, (operand.eval context row).isNull = false) →
      concatRows (some text) (items.map fun row => (operand.eval context row, none)) =
        some (text ++ (items.map fun row => 44 :: concatText (operand.eval context row)).flatten) := by
    intro text items
    induction items generalizing text with
    | nil => intro _; simp [concatRows]
    | cons row later ih =>
      intro notNull
      simp only [List.map_cons, concatRows, notNull row (List.mem_cons_self ..), Bool.false_eq_true, ite_false]
      rw [ih _ fun other member => notNull other (List.mem_cons_of_mem _ member)]
      simp [concatSeparator]
  simp only [Aggregate.eval, List.map_cons, groupConcatValue, concatRows, Option.map_none,
    present first (List.mem_cons_self ..), Bool.false_eq_true, ite_false]
  rw [joined _ rest fun row member => present row (List.mem_cons_of_mem _ member)]

end Belay.Sqlite.Model.Resolved
