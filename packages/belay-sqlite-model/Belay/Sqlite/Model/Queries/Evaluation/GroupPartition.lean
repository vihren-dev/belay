import Belay.Sqlite.Model.Queries.Evaluation.GroupsPairwise

set_option doc.verso true

/-! The partition that grouping makes (ADR 0027, D1, phase {lit}`group`): the fold of
{name}`Belay.Sqlite.Model.Resolved.groupStep` puts each row in exactly one group, each group starts
with a row that each of its later rows is the same as, and the first rows of two groups are not the
same. The laws hold for every test {lit}`same`; {lit}`GROUP BY` uses
{name}`Belay.Sqlite.Model.Resolved.sameGroup`. -/

namespace Belay.Sqlite.Model.Resolved

/-- Groups are formed for a test {lit}`same`: each group has a first row, and each later row of the
group is the same as the first row ({lit}`same later first`). -/
def GroupsFormed {α : Type} (same : α → α → Bool) (found : List (List α)) : Prop :=
  ∀ group ∈ found, ∃ first rest, group = first :: rest ∧ ∀ later ∈ rest, same later first = true

/-- The groups are apart for a test {lit}`same`: for every two groups that each have a first row,
the first row of the later group is not the same as the first row of the earlier group
({lit}`same later earlier = false`). A pair in which a group is empty has no condition. -/
def GroupsApart {α : Type} (same : α → α → Bool) (found : List (List α)) : Prop :=
  (found.map List.head?).Pairwise fun earlier later => ∀ e ∈ earlier, ∀ l ∈ later, same l e = false

/-- For every item, groups and index of a group: the groups after the item joins the group at the
index, one after the other, are a permutation of the groups before followed by the item. Proof
sketch: induction on the groups; the item moves past the later groups. -/
theorem flatten_modify_append_perm {α : Type} (row : α) :
    ∀ (found : List (List α)) (index : Nat), index < found.length →
      ((found.modify index (· ++ [row])).flatten).Perm (found.flatten ++ [row])
  | group :: rest, 0, _ => by
    simp only [List.modify_zero_cons, List.flatten_cons, List.append_assoc]
    exact List.Perm.append_left group List.perm_append_comm
  | group :: rest, index + 1, bound => by
    simp only [List.modify_succ_cons, List.flatten_cons, List.append_assoc]
    exact List.Perm.append_left group (flatten_modify_append_perm row rest index (by simpa using bound))

/-- For every test, groups and row: the groups after one step of grouping, one after the other, are a
permutation of the groups before followed by the row. Proof sketch: the row joins a group
({name}`flatten_modify_append_perm`) or starts a group at the end. -/
theorem groupStep_flatten_perm {α : Type} (same : α → α → Bool) (found : List (List α)) (row : α) :
    (groupStep same found row).flatten.Perm (found.flatten ++ [row]) := by
  unfold groupStep
  cases search : found.findIdx? (fun group => group.head?.any (same row)) with
  | none => simp
  | some index =>
    exact flatten_modify_append_perm row found index (List.findIdx?_eq_some_iff_getElem.mp search).1

/-- For every test, rows and groups: the groups after the steps of the rows, one after the other, are
a permutation of the groups before followed by the rows. Proof sketch: induction on the rows with
{name}`groupStep_flatten_perm`. -/
theorem groupFold_flatten_perm {α : Type} (same : α → α → Bool) :
    ∀ (rows : List α) (found : List (List α)),
      (rows.foldl (groupStep same) found).flatten.Perm (found.flatten ++ rows)
  | [], found => by simp
  | row :: rows, found => by
    refine (groupFold_flatten_perm same rows _).trans ?_
    simpa using (groupStep_flatten_perm same found row).append_right rows

/-- For every item, groups that each have a row, and index: the item joining the group at the index
changes no first row of a group. Proof sketch: induction on the groups; the item goes after the
first row of a group that has one. -/
theorem map_head?_modify_append {α : Type} (row : α) (found : List (List α)) (index : Nat)
    (nonempty : ∀ group ∈ found, group ≠ []) :
    (found.modify index (· ++ [row])).map List.head? = found.map List.head? := by
  apply List.ext_getElem (by simp)
  intro position first second
  simp only [List.getElem_map, List.getElem_modify]
  split
  · have := nonempty _ (List.getElem_mem (by simpa using second))
    obtain ⟨head, tail, same⟩ := List.ne_nil_iff_exists_cons.mp this
    simp [same]
  · rfl

/-- For every test, groups and row: when the groups are formed ({name}`GroupsFormed`), they stay formed
after one step of grouping. Proof sketch: a row that starts a group is its first row; a row that
joins a group joins one whose first row it is the same as. -/
theorem groupStep_formed {α : Type} (same : α → α → Bool) (found : List (List α)) (row : α)
    (formed : GroupsFormed same found) : GroupsFormed same (groupStep same found row) := by
  unfold groupStep
  cases search : found.findIdx? (fun group => group.head?.any (same row)) with
  | none =>
    intro group member
    rcases List.mem_append.mp member with old | new
    · exact formed group old
    · exact ⟨row, [], by simpa using new, by simp⟩
  | some index =>
    obtain ⟨bound, joins, -⟩ := List.findIdx?_eq_some_iff_getElem.mp search
    intro group member
    obtain ⟨position, inside, rfl⟩ := List.getElem_of_mem member
    rw [List.getElem_modify]
    have length : position < found.length := by simpa using inside
    obtain ⟨first, rest, shape, later⟩ := formed _ (List.getElem_mem length)
    split
    · rename_i sameIndex
      subst sameIndex
      refine ⟨first, rest ++ [row], by simp [shape], fun item inRest => ?_⟩
      rcases List.mem_append.mp inRest with old | new
      · exact later item old
      · simp only [List.mem_singleton] at new
        subst new
        simpa [shape] using joins
    · exact ⟨first, rest, shape, later⟩

/-- For every test, groups and row: when the groups are formed and apart ({name}`GroupsApart`), they
stay apart after one step of grouping. Proof sketch: joining a group changes no first row
({name}`map_head?_modify_append`); a new group starts only when the row is the same as no first
row. -/
theorem groupStep_apart {α : Type} (same : α → α → Bool) (found : List (List α)) (row : α)
    (formed : GroupsFormed same found) (apart : GroupsApart same found) :
    GroupsApart same (groupStep same found row) := by
  have nonempty : ∀ group ∈ found, group ≠ [] := fun group member => by
    obtain ⟨first, rest, rfl, -⟩ := formed group member
    simp
  unfold groupStep GroupsApart
  cases search : found.findIdx? (fun group => group.head?.any (same row)) with
  | none =>
    have fresh := List.findIdx?_eq_none_iff.mp search
    rw [List.map_append, List.pairwise_append]
    refine ⟨apart, by simp, fun earlier inEarlier later inLater => ?_⟩
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at inLater
    subst inLater
    obtain ⟨group, member, rfl⟩ := List.mem_map.mp inEarlier
    intro first isFirst row' isRow
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at isRow
    subst isRow
    have := fresh group member
    simp_all
  | some index =>
    rw [map_head?_modify_append row found index nonempty]
    exact apart

/-- For every test, rows and groups that are formed and apart: the groups after the steps of the rows
are formed and apart. Proof sketch: induction on the rows with {name}`groupStep_formed` and
{name}`groupStep_apart`. -/
theorem groupFold_formed_apart {α : Type} (same : α → α → Bool) :
    ∀ (rows : List α) (found : List (List α)), GroupsFormed same found → GroupsApart same found →
      GroupsFormed same (rows.foldl (groupStep same) found) ∧ GroupsApart same (rows.foldl (groupStep same) found)
  | [], _, formed, apart => ⟨formed, apart⟩
  | row :: rows, found, formed, apart =>
    groupFold_formed_apart same rows _ (groupStep_formed same found row formed)
      (groupStep_apart same found row formed apart)

end Belay.Sqlite.Model.Resolved
