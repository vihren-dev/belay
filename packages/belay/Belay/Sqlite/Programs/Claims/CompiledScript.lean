import Belay.Sqlite.Programs.Claims.LastOutput
import Belay.Sqlite.Programs.Claims.CompiledFilter
import Belay.Sqlite.Programs.StatementRunLaws.SelectCatalogExecution
import Belay.Sqlite.Schema.Dispatch.SelectCatalogExecution
import Belay.Sqlite.Programs.Scripts.KindRuleSend

set_option doc.verso true

/-! Scan plans and their certificates let callers compare a sequence of writes and a final scan
by the data that describes its last output. -/

namespace Belay.Sqlite.CompiledScript
open Model hiding Database

/-- Rows visible to a compiled table scan, including duplicates. -/
abbrev Rows := List (List Value)

/-- Read a table by its resolved catalog position. A DELETE can replace one such scan. -/
abbrev Sources := Nat → Rows

/-- Expose the rows of a raw model database to a compiled plan. -/
def scans (raw : Model.Database) (pos : Nat) : Rows :=
  ((raw.table pos).map Resolved.sourceRows).getD []

/-- Relate the execution context to the inputs of a plan at a statement boundary. -/
structure Inputs (catalog : Database) (s : ExecutionContext) (src : Sources) : Prop where
  /-- The connection has the resolve state of a fresh connection on the compilation catalog. -/
  names : s.connection.resolveState = (catalog.raw.connection {}).resolveState
  /-- The connection state holds {name}`Model.Database.Valid` for the pinned profile. -/
  valid : s.connection.state.Holds (Model.Database.Valid Profile.pinned)
  /-- The plan reads each table as the same bag of rows as the model. -/
  agree : ∀ pos, (scans s.connection.state.database pos).Perm (src pos)

/-- For a context and scan sources related by {name}`Inputs`, if the catalog has the
given table shape at a position, the connection has the table
with that shape and its stored rows there. Its source rows are a permutation of the plan input at that position.
Proof sketch: transfer the lookup along the catalog equality, then use the scan permutation. -/
theorem Inputs.table {catalog : Database} {s src} (inputs : Inputs catalog s src) {pos shape}
    (located : catalog.raw.catalog.tableAt pos = some shape) :
    let db := s.connection.state.database
    let table : Table := ⟨shape, db.rows.getD pos []⟩
    db.table pos = some table ∧ (Resolved.sourceRows table).Perm (src pos) := by
  have names : s.connection.state.database.catalog = catalog.raw.catalog :=
    congrArg ResolveState.catalog inputs.names
  have present : s.connection.state.database.table pos = some ⟨shape, s.connection.state.database.rows.getD pos []⟩ := by
    simp [Model.Database.table, names, located]
  exact ⟨present, by simpa [scans, present] using inputs.agree pos⟩

/-- Compile each projection before visiting rows. Scalar expressions reuse their bound
values, and aggregate outputs retain the model's single-row interpretation. -/
def compileColumn (args : List Value) : Resolved.Output → List Value → Value
  | .scalar e => let plan := CompiledExpr.compile args e; fun row => (plan.run row).1
  | .aggregate a => fun row => a.eval (.bound args) [row]

/-- The final operation of a normalized scan. Keep the projection as data so callers may
compare plans before evaluating them on a database. -/
inductive ScanOutput where
  /-- Count the rows affected by the final DELETE. -/
  | count
  /-- Project the selected rows using the final SELECT bindings. -/
  | project (columns : List Resolved.Output) (args : List Value)
  deriving DecidableEq

/-- Compile the projection once and apply it to each selected row. -/
def ScanOutput.run : ScanOutput → Rows → Output
  | .count => fun xs => .done xs.length
  | .project outputs args =>
    let columns := outputs.map (compileColumn args)
    fun xs => .rows (Resolved.normalForm (xs.map fun row => columns.map (fun f => f row)))

/-- Compute the final output from the table scans supplied by the preceding statements. -/
structure Plan where
  /-- Table that supplies the rows. -/
  pos : Nat
  /-- Combined selection over its original scan. -/
  filter : Filter
  /-- Return the row count or project and normalize the selected rows. -/
  finish : ScanOutput
  deriving DecidableEq

/-- Evaluate the compiled scan and its one final operation. -/
def Plan.run (p : Plan) (src : Sources) := p.finish.run (p.filter.rows (fun _ => src p.pos))

/-- A scan known to return no rows has no dependence on its input table or projected expressions. -/
def Plan.pruneEmpty (p : Plan) : Plan :=
  match p.filter with
  | none => ⟨0, none, match p.finish with | .count => .count | .project .. => .project [] []⟩
  | some _ => p

/-- Pruning an empty scan preserves its output. Proof sketch: the count is zero and the
projection of an empty list is empty, for every projection. -/
theorem Plan.run_pruneEmpty (p : Plan) (src : Sources) : p.pruneEmpty.run src = p.run src := by
  obtain ⟨pos, f, out⟩ := p
  cases f <;> cases out <;> rfl

/-- At every matching statement boundary, every execution ends with the predicted output. -/
def Checked (plan : Plan) (script : Script) (catalog : Database) : Prop :=
  ∀ s src, Inputs catalog s src →
    (send script).check (fun _ final => final.outputs.getLast? = some (plan.run src)) s

/-- Start a compiled plan on the input database and give its deterministic output profile. -/
def asLast (p : Plan) : LastOutputPlan := fun db _ =>
  let out := some (p.run db.scanAt)
  (out, fun o => out = o)

/-- A checked plan certifies the last output from a fresh connection. Proof sketch: use the
admitted database for the initial scans and lift the postcondition to all branches. -/
theorem correct {p : Plan} {s : Script} {catalog : Database} (checked : Checked p s catalog) :
    (asLast p).Correct s catalog := by
  intro db schema env _
  apply Script.lastOutputProfile_of_check
  exact checked _ db.scanAt ⟨Database.resolveState_of_catalog db catalog schema env.counters,
    ExecutionContext.initial_holds_valid db env, fun _ => .refl _⟩

end Belay.Sqlite.CompiledScript
