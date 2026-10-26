import Belay.Sqlite.Model.Resolution.QuerySourceExpansion
import Belay.Sqlite.Model.Resolution.RowSpec
import Belay.Sqlite.Model.Resolution.SourceListFromArms

set_option doc.verso true

/-! Ordinary source resolution cannot succeed for an unexpanded stored view. These
facts retain the identity preparation path of existing query-resolution laws. -/

namespace Belay.Sqlite.Model

/-- A successfully resolved reference without an indexed query or function
arguments does not find a stored view. Proof sketch: a physical table excludes a view in the shared
namespace; every remaining unexpanded view branch reports an issue. -/
theorem resolveReference_noView (catalog : Catalog) (path : List Nat)
    (reference : Syntax.TableReference) (queries : Nat → Except SourceIssue ScopeSource)
    (prefix_ : List Nat) (resolved : SourceItem × ScopeSource)
    (ok : resolveReference catalog path reference queries prefix_ = .ok resolved) :
    reference.namesStoredView catalog none = false := by
  unfold Syntax.TableReference.namesStoredView
  cases named : reference.query with
  | some index => simp
  | none =>
    cases schema : reference.schema with
    | some name => simp
    | none =>
      show (true && reference.arguments.isNone && (catalog.findView reference.table).isSome) = false
      cases table : catalog.findTable reference.table with
      | some found =>
        obtain ⟨position, shape⟩ := found
        simp [Catalog.findView_none_of_table table]
      | none =>
        cases view : catalog.findView reference.table with
        | none => simp
        | some found =>
          cases arguments : reference.arguments <;>
            simp [resolveReference, resolveReferenceTraced, named, schema, arguments, resolveTableReferenceTraced, table, view,
              refuseTable, traced_drop, Except.mapError, SourceIssue.under] at ok

/-- If all FROM references resolve, none of its named sources without arguments
is an unexpanded stored view. No FROM has no references, as in {name}`resolveSources`.
Proof sketch: successful source resolution gives a successful first reference and
one successful resolution per join; apply {name}`resolveReference_noView` to each. -/
theorem resolveSources_noView (catalog : Catalog) (source : Option Syntax.TableReference)
    (joins : List Syntax.Join) (start : Nat) (queries : Nat → Except SourceIssue ScopeSource)
    (prefix_ : List Nat) (pending : List PendingSource) (scope : Scope)
    (ok : resolveSources catalog source joins start queries prefix_ = .ok (pending, scope)) :
    (source.any fun first => (first :: joins.map (·.source)).any (·.namesStoredView catalog none)) = false := by
  cases source with
  | none => rfl
  | some source =>
    simp only [resolveSources_some, bind, Except.bind] at ok
    split at ok <;> try contradiction
    split at ok <;> try contradiction
    rename_i first firstOk
    split at ok <;> try contradiction
    rename_i joined joinedOk
    have firstNoView := resolveReference_noView catalog [1] source queries prefix_ first firstOk
    have joinNoView : ∀ join ∈ joins, join.source.namesStoredView catalog none = false := by
      intro join member
      obtain ⟨index, atIndex⟩ := List.getElem?_of_mem member
      have pairAt : (joins.zip (joins.map (joinOperator ·.operator)))[index]? =
          some (join, joinOperator join.operator) := by simp [List.getElem?_zip_eq_some, atIndex]
      obtain ⟨value, _, step⟩ := (resolveAllFrom_ok _ 0 _ joined joinedOk).2 index _ pairAt
      simp only [Nat.zero_add] at step
      split at step <;> try contradiction
      rename_i resolved referenceOk
      exact resolveReference_noView catalog [2, index, 1] join.source queries prefix_ resolved referenceOk
    simpa [firstNoView, List.any_map, List.any_eq_false] using joinNoView

/-- A query whose ordinary sources resolve needs no view copies. With no written
subqueries it also has no WITH definitions, so preparation keeps its query intact.
Proof sketch: {name}`resolveSources_noView` removes the only possible expansion trigger. -/
theorem querySourceCopiesNeeded_nil (catalog : Catalog) (query : Syntax.Subquery)
    (pending : List PendingSource) (scope : Scope)
    (ok : resolveSources catalog query.source query.joins = .ok (pending, scope)) :
    querySourceCopiesNeeded catalog query [] = false := by
  simpa [querySourceCopiesNeeded] using
    resolveSources_noView catalog query.source query.joins 0 _ [] pending scope ok

end Belay.Sqlite.Model
