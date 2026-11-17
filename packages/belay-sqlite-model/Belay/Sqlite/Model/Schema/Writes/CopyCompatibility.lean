import Belay.Sqlite.Model.Schema.Columns.CopyInsertRows
import Belay.Sqlite.Model.Schema.Rows.DatabaseConstraintChecks
import Belay.Sqlite.Model.Schema.Writes.CopyInsertFits
import Belay.Sqlite.Model.Tooling.Counterexamples.CopyInsertRows

set_option doc.verso true

/-! The catalog conditions under which the rows of a source table fit an empty target
when the copy carries an integer primary key. The conditions apply before the INSERT
executes, so the row theorem is independent of statement triggers and scan order. -/

namespace Belay.Sqlite.Model

/-- For two definitions and the target's unique keys, check width, storage affinities,
rowid alias and the constraints that copying can discharge from the schema. Every
target NOT NULL must already be required in the source. The caller supplies the
remaining STRICT typing premise for the actual rows. -/
def CatalogTable.copyCompatible (source target : CatalogTable) (keys : List UniqueKey) : Bool :=
  target.columns.map CatalogColumn.affinity == source.columns.map CatalogColumn.affinity &&
  (source.columns.zip target.columns).all (fun (old, new) => !new.notNull || old.notNull) &&
  source.rowidAlias == target.rowidAlias && LiteralData.aliasReady target &&
  target.columns.all (·.generated.isNone) && target.allChecks.isEmpty &&
  keys.all (fun key => target.rowidAlias.any (fun pos => key.terms == [{ term := .column pos }] && key.filter.isNone))

/-- For compatible definitions and a shared rowid alias, every permutation of the
admitted source rows fits an empty target if its cells meet the STRICT types. The
inserted rows, including their rowids, equal that permutation. The source must
satisfy its NOT NULL constraints. Proof sketch: equal affinities give equal widths
and stored cells. At a required target column, the zipped comparison supplies
the source's NOT NULL guarantee. The alias supplies rowid validity and uniqueness
in every scan order. Apply the row insertion and constraint laws for a copy. -/
theorem InsertFits.copy_compatible (ctx : Resolved.EvalContext) {source target : Table} {keys : List UniqueKey}
    {position : Nat} {rows : List Row} (compatible : source.shape.copyCompatible target.shape keys = true)
    (alias : source.shape.rowidAlias = some position) (empty : target.rows = [])
    (admitted : source.Admitted) (sourceNotNull : source.NotNull) (order : rows.Perm source.rows)
    (typed : ∀ row ∈ source.rows, LiteralData.typesFit target.shape row = true) :
    let values := insertSelectRows ctx target.shape.columns ((List.range target.shape.columns.length).map .source)
      (rows.map Row.values)
    InsertFits keys target values ∧ (LiteralData.inserted target values).rows = rows := by
  dsimp only
  simp only [CatalogTable.copyCompatible, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    Option.isNone_iff_eq_none, List.isEmpty_iff] at compatible
  obtain ⟨⟨⟨⟨⟨⟨affinities, required⟩, sameAlias⟩, ready⟩, plain⟩, noChecks⟩, onlyKey⟩ := compatible
  have targetAlias := sameAlias.symm.trans alias
  have width : target.shape.columns.length = source.shape.columns.length := by
    simpa using congrArg List.length affinities
  have aliased : ∀ row ∈ rows, row.values[position]? = some (.integer row.rowid) :=
    fun row member => admitted.rowsAliased row (order.mem_iff.mp member) position alias
  have wide : ∀ row ∈ rows, row.values.length = target.shape.columns.length :=
    fun row m => (admitted.rowsWide row (order.mem_iff.mp m)).trans width.symm
  have stored : ∀ row ∈ rows, row.Stored target.shape.columns :=
    fun row m => Row.Stored.of_affinities affinities (admitted.rowsStored row (order.mem_iff.mp m))
  rw [insertSelectRows_copy ctx _ _ (by simpa using wide) (by simpa [Row.Stored] using stored)]
  refine ⟨InsertFits.copy keys target position rows empty targetAlias ready plain
    (fun row m => typed row (order.mem_iff.mp m)) noChecks ?_ aliased wide stored ?_
    ((order.map Row.rowid).nodup_iff.mpr admitted.rowidsDistinct)
    (fun row m => admitted.rowidsInRange row (order.mem_iff.mp m)),
    congrArg Table.rows (LiteralData.inserted_copy target position rows empty targetAlias plain aliased)⟩
  · intro key m
    simpa [targetAlias] using onlyKey key m
  · intro row m i new value atNew atValue needed
    have inside := (List.getElem?_eq_some_iff.mp atNew).1
    have oldInside : i < source.shape.columns.length := width ▸ inside
    have atOld := List.getElem?_eq_getElem oldInside
    have pair : (source.shape.columns.zip target.shape.columns)[i]? = some (source.shape.columns[i], new) :=
      List.getElem?_zip_eq_some.mpr ⟨atOld, atNew⟩
    have prior := required _ (List.mem_iff_getElem?.mpr ⟨i, pair⟩)
    exact sourceNotNull row (order.mem_iff.mp m) i _ value atOld atValue (by simpa [needed] using prior)

end Belay.Sqlite.Model
