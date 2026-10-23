import Belay.Sqlite.Model.KeysUniqueRowUpdate
import Belay.Sqlite.Model.KeysUniqueRowInsert
import Belay.Sqlite.Model.KeysUniqueDrop
import Belay.Sqlite.Model.ForeignKeyWrites

set_option doc.verso true

/-! The row engine keeps the atom "keys unique" (ADR 0022, D3, slice 2): {lit}`runRows` keeps
the invariant of the row engine at every fuel, and so the writes through it
({lit}`insertKeys`, {lit}`updateKeys`, {lit}`deleteKeys`, {lit}`dropKeys`) give effects whose
databases satisfy the atom. -/

namespace Belay.Sqlite.Model

/-- For every catalog, links and fuel: {name}`runRows` keeps the invariant of the row engine
({name}`NestedRun.KeepsKeys`). Proof sketch: induction on the fuel; without fuel the work is
undescribed; with fuel, the rows of the work run in a fold of {name}`deleteRow_keysUnique`,
{name}`updateRow_keysUnique` or {name}`insertRow_keysUnique`, whose nested writes run with one
less fuel and keep the invariant by induction. -/
theorem runRows_keysUnique (catalog : Catalog) (links : List ForeignKeyLink) :
    ∀ fuel, NestedRun.KeepsKeys catalog (runRows catalog links fuel)
  | 0 => fun _ _ _ _ => trivial
  | fuel + 1 => fun frame work state unique => by
    have nested := runRows_keysUnique catalog links fuel
    cases work with
    | delete position rowids record ignore fire =>
      simp only [runRows]
      exact ResultHolds.foldlM (fun reached rowid held =>
        deleteRow_keysUnique nested frame position record ignore fire held rowid) rowids state unique
    | update position change assigned changed rowids record =>
      simp only [runRows]
      exact ResultHolds.foldlM (fun reached rowid held =>
        updateRow_keysUnique nested frame position change assigned changed record held rowid) rowids state unique
    | insert position rows policy clauses multiWrite record =>
      simp only [runRows]
      exact ResultHolds.foldlM (fun reached values held =>
        insertRow_keysUnique nested frame position policy clauses multiWrite record held values) rows state unique

/-- For every input database, target, flag and result of the row engine: if the input database
satisfies {name}`Database.KeysUnique` and the result keeps the invariant over the input catalog
(a success satisfies {name}`KeyState.KeysUnique` and a stop {name}`KeyStop.KeysUnique`), the
database of the effect of {name}`keyRun` ({name}`effectDatabase`) satisfies
{name}`Database.KeysUnique`. Proof sketch: that database is the input database or the database
of the reached state. -/
theorem keyRun_keysUnique {input : Database} (unique : input.KeysUnique) (target : Nat) (plain : Bool)
    {result : Except KeyStop KeyState}
    (holds : ResultHolds (KeyState.KeysUnique input.catalog) (KeyStop.KeysUnique input.catalog) result) :
    (effectDatabase (keyRun input target plain result).effect).KeysUnique := by
  unfold keyRun
  repeat' split
  all_goals first | exact unique | (subst_vars; exact holds) | skip
  all_goals simp_all [effectDatabase, ResultHolds, KeyStop.KeysUnique, KeyState.KeysUnique]

/-- For every rules, clock value, target, work, database, flag and algorithm: if the database
satisfies {name}`Database.KeysUnique`, the database of the effect of {name}`rowsKeys` satisfies
it. Proof sketch: {name}`keyRun_keysUnique` of {name}`runRows_keysUnique` from the state with the
rows of the database ({name}`KeyState.keysUnique_start`). -/
theorem rowsKeys_keysUnique (rules : Resolved.WriteRules) (clock : Int) (target : Nat) (work : RowWork)
    {database : Database} (unique : database.KeysUnique) (plain : Bool) (algorithm : Option ConflictAlgorithm) :
    (effectDatabase (rowsKeys rules clock target work database plain algorithm).effect).KeysUnique :=
  keyRun_keysUnique unique target plain
    (runRows_keysUnique _ _ _ _ work _ (KeyState.keysUnique_start unique))

/-- For every rules, clock value, positions and database: if the database satisfies
{name}`Database.KeysUnique` and its catalog meets the condition of DROP at the positions
({name}`Catalog.DropCondition`), the database of the effect of {name}`dropKeys` satisfies it.
Proof sketch: the DELETE of the rows is {name}`rowsKeys_keysUnique`; after it the catalog is the
input catalog ({name}`keyRun_ok_catalog`), so the drop is {name}`Database.KeysUnique.drop`. -/
theorem dropKeys_keysUnique (rules : Resolved.WriteRules) (clock : Int) (positions : List Nat)
    {database : Database} (unique : database.KeysUnique) (condition : database.catalog.DropCondition positions) :
    (effectDatabase (dropKeys rules clock positions database).effect).KeysUnique := by
  unfold dropKeys
  split
  · dsimp only
    split
    · rename_i target _ table _ _ after deleted
      have afterUnique := rowsKeys_keysUnique rules clock target
        (.delete target (table.scanRows.map (·.rowid)) false true false) unique true none
      rw [deleted] at afterUnique
      have sameCatalog := keyRun_ok_catalog deleted
      exact Database.KeysUnique.drop afterUnique (sameCatalog ▸ condition)
    · exact rowsKeys_keysUnique rules clock _ _ unique true none
  · exact Database.KeysUnique.drop unique condition

end Belay.Sqlite.Model
