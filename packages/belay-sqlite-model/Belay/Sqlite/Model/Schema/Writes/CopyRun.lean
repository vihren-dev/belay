import Belay.Sqlite.Model.Schema.Writes.CopyCompatibility
import Belay.Sqlite.Model.Schema.Writes.CopyProductions
set_option doc.verso true

/-! The result of a full-column INSERT from SELECT into an empty compatible table
with a shared rowid alias and no resolved write rules. -/

namespace Belay.Sqlite.Model

/-- The model's own row order is the first access order. The fold can only append
further index orders, which preserves the head. -/
private theorem scanFirst (catalog : Catalog) (pos : Nat) (table : Table) :
    ∃ rest, Table.accessOrders catalog pos table = table.scanRows :: rest := by
  let add := fun (found : List (List Row)) (order : List Row) =>
    if found.any (fun other => other.map (·.rowid) == order.map (·.rowid)) then found else found ++ [order]
  have keep (orders : List (List Row)) (tail : List (List Row)) :
      ∃ rest, orders.foldl add (table.scanRows :: tail) = table.scanRows :: rest := by
    induction orders generalizing tail with
    | nil => exact ⟨tail, rfl⟩
    | cons head rest ih =>
      unfold List.foldl
      dsimp only [add]
      split
      · exact ih tail
      · exact ih (tail ++ [head])
  exact keep _ []

/-- For any clock, counters, parameters, names, database and two tables at the given positions,
copy every column with {name}`Resolved.Query.copyOf` and an INSERT without write rules,
conflict clauses, subqueries or RETURNING. Suppose the source satisfies {name}`Table.Admitted`
and {name}`Table.NotNull`, the target is empty, the shapes and target keys pass
{name}`CatalogTable.copyCompatible`, the source has a rowid alias, and every source row
satisfies {name}`LiteralData.typesFit` for the target. Then:
* the run is ready;
* it succeeds with exactly the source rows, in {name}`Table.scanRows` order, at the target;
* a single access order gives no alternatives;
* every alternative succeeds with a permutation of the source rows at the target.
Each effect uses {name}`Database.setRows`, so it retains every other table and the catalog.
Proof sketch: the first scan is the table scan and every other access order permutes it.
{name}`Resolved.Query.productions_copyOf` projects its cells. For each production,
{name}`InsertFits.copy_compatible` gives the copied rows and {name}`insertSelectOutcome_fits`
gives the effect. A shared rowid alias rules out a separate transfer of implicit rowids. -/
theorem runStatement_copyOf (clock : Int) (counters : Counters) (parameters : List Value) (database : Database)
    (s t : Nat) (source target : Table) (names : List String) {aliasPos : Nat}
    (src : database.table s = some source) (dst : database.table t = some target)
    (compatible : source.shape.copyCompatible target.shape (database.keys t target) = true)
    (alias : source.shape.rowidAlias = some aliasPos) (empty : target.rows = [])
    (admitted : source.Admitted) (notNull : source.NotNull)
    (typed : ∀ row ∈ source.rows, LiteralData.typesFit target.shape row = true) :
    let cells := (List.range target.shape.columns.length).map Resolved.SourceCell.source
    let query := Resolved.Query.copyOf s source.shape.columns.length names
    let run := runStatement clock counters parameters (.insertSelect t cells query [] [] none [] none) database
    run.ready = true ∧ run.effect = .ok (database.setRows t source.scanRows) ∧
      (Table.accessOrders database.catalog s source = [source.scanRows] → run.alternatives = []) ∧
      ∀ alt ∈ run.alternatives, ∃ rows, rows.Perm source.rows ∧ alt.effect = .ok (database.setRows t rows) := by
  let ctx := Resolved.statementContext clock counters parameters database []
  let cells := (List.range target.shape.columns.length).map Resolved.SourceCell.source
  let query := Resolved.Query.copyOf s source.shape.columns.length names
  let prod := fun order : List Row => ({ rows := order.map Row.values, failure := none } : SourceProduction)
  let outcome := insertSelectOutcome clock ctx database t target cells [] none none true
  have effect (rows : List Row) (perm : rows.Perm source.rows) :
      (outcome (prod rows)).effect = .ok (database.setRows t rows) ∧ (outcome (prod rows)).ready = true := by
    obtain ⟨fits, copied⟩ := InsertFits.copy_compatible ctx compatible alias empty admitted notNull perm typed
    obtain ⟨eff, ready, _⟩ := insertSelectOutcome_fits clock ctx database t target cells [] none true _ fits rfl
    exact ⟨eff.trans (congrArg (fun rs => (Except.ok (database.setRows t rs) : Effect)) copied), ready⟩
  obtain ⟨tail, orders⟩ := scanFirst database.catalog s source
  let others := ((tail.map prod).filter (fun p => !(p == prod source.scanRows))).eraseDups
  have prods : query.productions ctx database (!Resolved.Statement.collectsSource t query [] [] none) =
      some (prod source.scanRows :: others) := by
    rw [Resolved.Query.productions_copyOf _ _ _ _ _ _ (fun _ _ => ⟨rfl, rfl, rfl⟩) src admitted, orders]
    change some ((prod source.scanRows :: tail.map prod).eraseDups) = _
    rw [List.eraseDups_cons]
  have other (p : SourceProduction) (m : p ∈ others) :
      ∃ rows, rows.Perm source.rows ∧ (outcome p).effect = .ok (database.setRows t rows) ∧ (outcome p).ready = true := by
    obtain ⟨rows, member, rfl⟩ := List.mem_map.mp (List.mem_filter.mp (List.mem_eraseDups.mp m)).1
    have perm := Table.accessOrders_perm database.catalog s source admitted.rowidsDistinct rows
      (orders ▸ List.mem_cons_of_mem _ member)
    exact ⟨rows, perm, effect rows perm⟩
  have main := effect source.scanRows source.scanRows_perm
  have ready : (others.map outcome).all (fun item => item.ready && item.effect.isModeled) = true := by
    apply List.all_eq_true.mpr
    intro item member
    obtain ⟨p, m, rfl⟩ := List.mem_map.mp member
    obtain ⟨_, _, eff, ok⟩ := other p m
    simp [eff, ok, Effect.isModeled]
  have targetAlias : target.shape.rowidAlias = some aliasPos := by
    simp only [CatalogTable.copyCompatible, Bool.and_eq_true, beq_iff_eq] at compatible
    exact compatible.1.1.1.1.2.symm.trans alias
  have transfer : insertSelectTransferRowids t cells query target database none = none := by
    simp [insertSelectTransferRowids, query, Resolved.Query.copyOf, Resolved.Query.simple,
      Resolved.QuerySource.first, targetAlias]
  change (insertSelectRun clock counters parameters t cells query [] [] none [] none database).ready = true ∧ _
  change _ ∧ (insertSelectRun clock counters parameters t cells query [] [] none [] none database).effect = _ ∧
    (_ → (insertSelectRun clock counters parameters t cells query [] [] none [] none database).alternatives = []) ∧
    ∀ alt ∈ (insertSelectRun clock counters parameters t cells query [] [] none [] none database).alternatives, _
  unfold insertSelectRun
  dsimp only [ctx] at prods
  simp only [dst, prods]
  refine ⟨?_, main.1, ?_, ?_⟩
  · change (((outcome (prod source.scanRows)).ready && (others.map outcome).all _ && _) && _ && _ && _ && _) = true
    rw [main.2, ready, transfer]
    have projected : (cells.filterMap fun | .cell fixed => some fixed | .source _ => none) = [] := by
      simp [cells, List.filterMap_map, Function.comp_def]
    have fixed : Resolved.cellsReady ctx [cells.filterMap fun | .cell f => some f | .source _ => none] = true := by
      rw [projected]
      rfl
    rw [Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨rfl, fixed⟩, rfl⟩
  · intro one
    rw [orders] at one
    obtain rfl := (List.cons.inj one).2
    rfl
  · intro alt m
    change alt ∈ (others.map outcome).map _ at m
    obtain ⟨item, im, rfl⟩ := List.mem_map.mp m
    obtain ⟨p, pm, rfl⟩ := List.mem_map.mp im
    obtain ⟨rows, perm, eff, _⟩ := other p pm
    exact ⟨rows, perm, eff⟩

end Belay.Sqlite.Model
