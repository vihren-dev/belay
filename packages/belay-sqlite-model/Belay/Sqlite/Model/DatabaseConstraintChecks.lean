import Belay.Sqlite.Model.DatabaseConstraints
import Belay.Sqlite.Model.DatabaseFactChecks

set_option doc.verso true

/-! The checks that decide the facts of a valid database (ADR 0022, D1): the checks of
{lit}`LiteralData.constraints`, with a lemma that each gives {lean}`true` exactly when its fact
holds, and {lit}`Decidable` instances through them, so {lit}`decide +kernel` proves
{lit}`Database.Valid`, or its negation, for a concrete database. -/

namespace Belay.Sqlite.Model

/-- For every two lists and every property of pairs: the property holds for every pair of the
zip of the lists exactly when it holds for the elements at every position at which both lists
have one. -/
theorem zip_forall_iff {α β} (first : List α) (second : List β) (property : α × β → Prop) :
    (∀ pair ∈ first.zip second, property pair) ↔
      ∀ (position : Nat) a b, first[position]? = some a → second[position]? = some b → property (a, b) := by
  simp only [List.mem_iff_getElem?, List.getElem?_zip_eq_some]
  exact ⟨fun all position a b atFirst atSecond => all (a, b) ⟨position, atFirst, atSecond⟩,
    fun all ⟨a, b⟩ ⟨position, atFirst, atSecond⟩ => all position a b atFirst atSecond⟩

/-- For every key and rows, {name}`LiteralData.uniqueRows` is {lean}`true` exactly when no row
conflicts with a later row on the key. Proof sketch: induction over the rows. -/
theorem uniqueRows_iff (key : UniqueKey) (rows : List Row) :
    LiteralData.uniqueRows key rows = true ↔ rows.Pairwise fun first second => LiteralData.keyEqual key first second = false := by
  induction rows with
  | nil => simp [LiteralData.uniqueRows]
  | cons row rest rest_iff =>
    simp only [LiteralData.uniqueRows, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, rest_iff,
      List.pairwise_cons, Bool.not_eq_true]

/-- For every table, {name}`LiteralData.notNullRows` is {lean}`true` exactly when the table
satisfies {name}`Table.NotNull`. -/
theorem Table.notNullRows_iff (table : Table) : LiteralData.notNullRows table = true ↔ table.NotNull := by
  simp only [LiteralData.notNullRows, Table.NotNull, List.all_eq_true, zip_forall_iff]
  refine forall_congr' fun row => imp_congr_right fun _ => forall_congr' fun position =>
    forall_congr' fun column => forall_congr' fun value => imp_congr_right fun _ => imp_congr_right fun _ => ?_
  cases column.notNull <;> simp

/-- For every table, {name}`LiteralData.typedRows` is {lean}`true` exactly when the table
satisfies {name}`Table.TypesFit`. -/
theorem Table.typedRows_iff (table : Table) : LiteralData.typedRows table = true ↔ table.TypesFit := by
  simp only [LiteralData.typedRows, LiteralData.typesFit, Table.TypesFit, List.all_eq_true, zip_forall_iff]

/-- For every table, {name}`LiteralData.checkedRows` is {lean}`true` exactly when the table
satisfies {name}`Table.ChecksHold`. -/
theorem Table.checkedRows_iff (table : Table) : LiteralData.checkedRows table = true ↔ table.ChecksHold := by
  simp only [LiteralData.checkedRows, LiteralData.checksHold, Table.ChecksHold, List.all_eq_true]

/-- For every keys and table, {name}`LiteralData.keysUnique` is {lean}`true` exactly when the
table satisfies {name}`Table.KeysUnique` for the keys. -/
theorem Table.keysUnique_iff (keys : List UniqueKey) (table : Table) :
    LiteralData.keysUnique keys table = true ↔ table.KeysUnique keys := by
  simp only [LiteralData.keysUnique, Table.KeysUnique, List.all_eq_true, uniqueRows_iff]

/-- For every keys and table, {name}`LiteralData.constraints` is {lean}`true` exactly when the
table satisfies {name}`Table.NotNull`, {name}`Table.TypesFit`, {name}`Table.ChecksHold` and
{name}`Table.KeysUnique` for the keys: the writes check the facts of a valid table. -/
theorem Table.constraints_iff (keys : List UniqueKey) (table : Table) :
    LiteralData.constraints keys table = true ↔
      table.NotNull ∧ table.TypesFit ∧ table.ChecksHold ∧ table.KeysUnique keys := by
  simp only [LiteralData.constraints, Bool.and_eq_true, Table.notNullRows_iff, Table.typedRows_iff,
    Table.checkedRows_iff, Table.keysUnique_iff, and_assoc]

/-- Decide {name}`Database.NotNull` with {name}`LiteralData.notNullRows`. -/
instance Database.decidableNotNull (database : Database) : Decidable database.NotNull :=
  database.decideEveryTable (fun _ table => LiteralData.notNullRows table) fun _ => Table.notNullRows_iff

/-- Decide {name}`Database.TypesFit` with {name}`LiteralData.typedRows`. -/
instance Database.decidableTypesFit (database : Database) : Decidable database.TypesFit :=
  database.decideEveryTable (fun _ table => LiteralData.typedRows table) fun _ => Table.typedRows_iff

/-- Decide {name}`Database.ChecksHold` with {name}`LiteralData.checkedRows`. -/
instance Database.decidableChecksHold (database : Database) : Decidable database.ChecksHold :=
  database.decideEveryTable (fun _ table => LiteralData.checkedRows table) fun _ => Table.checkedRows_iff

/-- Decide {name}`Database.KeysUnique` with {name}`LiteralData.keysUnique` of each table's keys. -/
instance Database.decidableKeysUnique (database : Database) : Decidable database.KeysUnique :=
  database.decideEveryTable (fun position table => LiteralData.keysUnique (database.catalog.uniqueKeys position table.shape) table)
    fun _ table => Table.keysUnique_iff _ table

/-- Decide {name}`Database.Valid` through the decisions of its fields. -/
instance Database.decidableValid (profile : Profile) (database : Database) : Decidable (database.Valid profile) :=
  decidable_of_iff (database.Admitted profile ∧ database.NotNull ∧ database.ChecksHold ∧ database.TypesFit ∧
      database.KeysUnique)
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

end Belay.Sqlite.Model
