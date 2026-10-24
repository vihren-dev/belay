import Belay.Sqlite.Model.Resolution.ScopeNames

set_option doc.verso true

/-! Laws of name resolution over a scope ({lit}`Scope.resolveName`): without right and full
joins, a name reads one column, at every depth of a subquery's scope. -/

namespace Belay.Sqlite.Model

/-- Whether a name resolution reads only its first column: missing, ambiguous, or found
with the one position of its first column. -/
def NameResolution.single : NameResolution → Prop
  | .found first reads => reads = [first]
  | .missing | .ambiguous => True

/-- For every name, result and source that keeps the left result ({name}`MergeRule.keepLeft`),
if the result reads only its first column ({name}`NameResolution.single`), so does the result
after the source ({name}`Scope.resolveStep`). Proof sketch: a merged column under
{name}`MergeRule.keepLeft` keeps the result, and any other later column makes the name
ambiguous. -/
theorem resolveStep_single (name : Identifier) (state : NameResolution) (source : ScopeSource)
    (holds : state.single) (rule : source.mergeRule = .keepLeft) : (Scope.resolveStep name state source).single := by
  unfold Scope.resolveStep
  split
  · exact holds
  · simp [NameResolution.single]
  · simp [NameResolution.single]
  · split
    · simp only [rule]; exact holds
    · first | (simp [NameResolution.single]; done) | simpa [NameResolution.single] using holds

/-- For every scope whose sources all keep the left result ({name}`MergeRule.keepLeft`), as
in a {lit}`FROM` without right and full joins, and every name, the resolution of the name
reads only its first column ({name}`NameResolution.single`): a name is one column, as in
slice 4b. Proof sketch: the resolution at each depth folds {name}`resolveStep_single` over the
sources, and the resolution of the name is the one of some depth, or missing. -/
theorem resolveName_single (scope : Scope) (keep : ∀ source ∈ scope, source.mergeRule = .keepLeft)
    (name : Identifier) : (scope.resolveName name).single := by
  have level : ∀ depth, (scope.resolveAt name depth).single := by
    intro depth
    have step : ∀ (sources : Scope) (state : NameResolution), state.single →
        (∀ source ∈ sources, source.mergeRule = .keepLeft) →
        (sources.foldl (fun result source =>
          if source.namesVisible && source.depth == depth && !source.trigger then Scope.resolveStep name result source else result) state).single := by
      intro sources
      induction sources with
      | nil => intro state holds _; exact holds
      | cons source rest ih =>
        intro state holds keeps
        apply ih _ _ fun other member => keeps other (List.mem_cons_of_mem _ member)
        dsimp only
        split
        · exact resolveStep_single name state source holds (keeps source List.mem_cons_self)
        · exact holds
    exact step scope .missing trivial keep
  unfold Scope.resolveName
  cases found : ((List.range scope.depths).map (scope.resolveAt name)).find? (· != .missing) with
  | none => trivial
  | some result =>
    have member := List.mem_of_find?_eq_some found
    simp only [List.mem_map] at member
    obtain ⟨depth, _, same⟩ := member
    simpa [← same] using level depth

end Belay.Sqlite.Model
