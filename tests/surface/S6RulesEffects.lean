import Belay

/-! A fixture module of `tests/surface_s6_rules_test.py`: the effect rules of ADR 0017, S6, used on small programs.
The package holds only the general rules. The tables, statements and claims are part of this fixture. An UPDATE and
an ADD COLUMN are checked through the rules for the stored rows of one statement, as conditional fresh-run claims
for every complete environment. The UPDATE is also checked as a total claim. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace S6RulesEffects
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- Two tables, with one item. The items are at position 0 and the audit notes at position 1. -/
def sample : Database := db! r"
  CREATE TABLE items(id INTEGER PRIMARY KEY, qty INTEGER);
  CREATE TABLE audit(note TEXT);
  INSERT INTO items VALUES(1, 5);"

/-- The update of the quantity of the item with a given id. -/
def bump : Script := sql r"UPDATE items SET qty = qty + 1 WHERE id = ?1" (Value.integer 1)

/-- The one statement of the update. -/
def bumpStatement : Syntax.Statement := (bump.statements.head (by decide +kernel)).1

/-- The resolved update: it assigns column 1 and keeps the rows whose column 0 equals parameter 1. -/
def bumpResolved : Resolved.Statement :=
  .update 0 [(1, .arithmetic .add (.column 1) (.literal (.integer 1)))]
    (some (.compare .eq (some .integer) (.column 0) (.parameter 1) .binary)) [] [] none

/-- The items table of {name}`sample`. -/
def itemsTable : Table := (sample.raw.table 0).get (by decide +kernel)

/-- {name}`sample` has {name}`itemsTable` at position 0. Proof sketch: by definition of the table. -/
theorem sample_items : sample.raw.table 0 = some itemsTable := (Option.some_get _).symm

/-- The values of the rows of the table at a position. -/
def tableValues (position : Nat) (connection : Connection) : List (List Value) :=
  (connection.state.database.rowsAt position).map (·.values)

/-- For every complete environment, every run of the update that has no error ends with the rows
{lit}`[[1, 6]]` in the items table. The claim holds for the one database {name}`sample`. A run with an error
needs nothing. Proof sketch: {name}`Sql.ifOk_send_plainUpdate` reduces the claim to the rows that
{name}`LiteralData.updated` computes; the statement resolves to {name}`bumpResolved` and the step is modeled
for every environment, so kernel evaluation gives the rows. -/
theorem bump_stores_new_quantity :
    FreshEnsures (send bump) (fun db => db = sample)
      (ifOk (fun final => ⌜tableValues 0 final.connection = [[.integer 1, .integer 6]]⌝ : ContextAssertion)) := by
  refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_
  rintro db rfl env _
  obtain ⟨after, found⟩ : ∃ after, resolveStatement runContext (sample.raw.connection env.counters).resolveState
      bumpStatement = .ok (bumpResolved, after) := ⟨_, rfl⟩
  have modeled : RunStep.continues (runScriptStep runContext env.clock 0 (sample.raw.connection env.counters)
      bumpStatement [.integer 1]) = true := rfl
  refine Sql.ifOk_send_plainUpdate (statement := bumpStatement) (values := [.integer 1]) found sample_items
    (RunStep.continues_iff.1 modeled) ?_
  intro value outputs final reached _ _
  show tableValues 0 final.connection = _
  unfold tableValues
  rw [reached]
  rfl

/-- For every complete environment, every run of the update ends with the rows {lit}`[[1, 6]]` in the items
table, and no run has an error or stops without a result. The claim holds for the one database
{name}`sample`. In plain words, this is the total form of {name}`bump_stores_new_quantity`: the update also
succeeds. Proof sketch: the step of the update is modeled and gives the count of one change for every
environment, which is not an error and not a choice, so {name}`check_send_single_of_step` leaves the
claim about the next context; {name}`plainUpdate_database` gives its database and kernel evaluation gives the
rows. -/
theorem bump_succeeds_with_new_quantity :
    FreshEnsures (send bump) (fun db => db = sample)
      (andOk (fun final => ⌜tableValues 0 final.connection = [[.integer 1, .integer 6]]⌝ : ContextAssertion)) := by
  refine (FreshEnsures.andOkWith_iff _ _ _).2 ?_
  rintro db rfl env _
  obtain ⟨after, found⟩ : ∃ after, resolveStatement runContext (sample.raw.connection env.counters).resolveState
      bumpStatement = .ok (bumpResolved, after) := ⟨_, rfl⟩
  obtain ⟨next, step⟩ : ∃ next, runScriptStep runContext env.clock 0 (sample.raw.connection env.counters)
      bumpStatement [.integer 1] = .continued (.done 1) next [] := ⟨_, rfl⟩
  refine (check_send_single_of_step (state := ExecutionContext.initial sample env) step
    (by intro alternatives same; cases same)).2 ⟨rfl, ?_⟩
  obtain ⟨value, -, stored⟩ := plainUpdate_database found sample_items step rfl
  show tableValues 0 next = _
  unfold tableValues
  rw [show next.state.database = _ from stored]
  rfl

-- The ADD COLUMN with a default value.

/-- The addition of a text column with a default value to the items. -/
def addNote : Script := sql r"ALTER TABLE items ADD COLUMN note TEXT DEFAULT 'x'"

/-- The one statement of the addition. -/
def addNoteStatement : Syntax.Statement := (addNote.statements.head (by decide +kernel)).1

/-- The column that the addition resolves to. -/
def noteColumn : CatalogColumn :=
  { name := name! "note", declaredType := some "TEXT"
    defaultValue := some ⟨.literal (.value (.text [120])) (.text [120]), "'x'"⟩ }

/-- For every complete environment, every run of the addition that has no error ends with the cells
{lit}`[1, 5, 'x']` in the one row of the items table: the new column holds its default value in the old row.
The claim holds for the one database {name}`sample`. Proof sketch: {name}`Sql.ifOk_send_addColumn` reduces the
claim to the database with the column appended and the default value read from the column; the default is
the text {lit}`'x'` and does not read the clock, which kernel evaluation shows, so the cells follow. -/
theorem add_note_keeps_old_cells :
    FreshEnsures (send addNote) (fun db => db = sample)
      (ifOk (fun final => ⌜tableValues 0 final.connection = [[.integer 1, .integer 5, .text [120]]]⌝
        : ContextAssertion)) := by
  refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_
  rintro db rfl env _
  obtain ⟨after, found⟩ : ∃ after, resolveStatement runContext (sample.raw.connection env.counters).resolveState
      addNoteStatement = .ok (.addColumn 0 noteColumn false, after) := ⟨_, rfl⟩
  have modeled : RunStep.continues (runScriptStep runContext env.clock 0 (sample.raw.connection env.counters)
      addNoteStatement []) = true := rfl
  refine Sql.ifOk_send_addColumn (statement := addNoteStatement) (values := []) found sample_items
    (RunStep.continues_iff.1 modeled) ?_
  intro value outputs final _ readDefault reached _ _
  have clockFree : noteColumn.clockDefault = false := rfl
  have stored : readDefaultValue noteColumn = .ok (.text [120]) := rfl
  rw [readDefault clockFree] at stored
  cases Except.ok.inj stored
  show tableValues 0 final.connection = _
  unfold tableValues
  rw [reached]
  rfl

#print axioms bump_stores_new_quantity
#print axioms bump_succeeds_with_new_quantity
#print axioms add_note_keeps_old_cells

end S6RulesEffects
