import Belay.Sqlite.NormalizedFieldPlan
import Belay.Sqlite.ScopedRowSteps
import Belay.Sqlite.ScopedSimulation

set_option doc.verso true

/-! Lookups across the lowercase-field expansion as a scoped simulation (ADR 0017, S8). The interface
has one call: the lookup of an id by a value. Its old entry reads {lit}`WHERE lower(source) = lower(?1)`
and its new entry reads {lit}`WHERE stored = lower(?1)`. The relation between an old context and a new
context names the clock, the expansion facts of the old connection, and the expanded database of the new
connection. It names no counter, no statement index and no output trace. The relation holds at the
migrated context of every successful expansion, and each lookup keeps it. The lookup theorem therefore
covers every application over this interface, including one that chooses its later lookups from earlier
results, on every database with a site. A write, a counter read or a change of the connection outside
the relation is outside this theorem. -/

namespace Belay.Sqlite.NormalizedFieldExpansion
open Belay.Sqlite.Calls Belay.Sqlite.Model Belay.Sqlite.Model.NormalizedField

/-- For every plan, clock, pair of indices, pair of connections, connection with the expansion facts, and
value: if the second connection has the expanded database of the first, then the original lookup on the
first connection gives some rows and keeps the connection, and the stored lookup on the second connection
gives the same rows and keeps its connection. The indices and the other parts of the connections are
arbitrary. Proof sketch: {name}`translate_step_outputs` equates the two outputs; the original lookup
resolves to a simple table query ({name}`resolve_original_lookup`), so its output is rows
({name}`step_output_of_simple_query`); {name}`runScriptStep_select_rows` finishes both. -/
theorem Plan.lookup_steps (plan : Plan) (clock : Option Clock) (before after : Nat)
    (connection expanded : Connection) (source : plan.Source connection)
    (reached : expanded.state.database = source.expanded) (value : Value) :
    ∃ rows, runScriptStep runContext clock before connection
        (originalLookup (tableReference plan.tableName plan.alias) plan.idName plan.sourceName plan.text
          plan.number) [value] = .continued (.rows rows) connection [] ∧
      runScriptStep runContext clock after expanded
        (storedLookup (tableReference plan.tableName plan.alias) plan.idName plan.storedName plan.text
          plan.number) [value] = .continued (.rows rows) expanded [] := by
  have same := translate_step_outputs runContext clock before after connection expanded
    (tableReference plan.tableName plan.alias) plan.idName plan.sourceName plan.storedName plan.text plan.number
    value source.site.table source.site.position source.site.source source.site.id plan.first plan.second rfl
    rfl rfl source.site.found source.site.present source.aligned source.site.fresh source.site.idFound
    source.site.sourceFound source.wide source.aliased source.site.keysInside source.site.plain reached
  obtain ⟨names, original⟩ := resolve_original_lookup runContext connection.resolveState
    (tableReference plan.tableName plan.alias) source.site.position source.site.table.shape plan.idName
    plan.sourceName plan.text plan.number rfl rfl rfl source.site.found source.site.idFound
    source.site.sourceFound
  have rows := step_output_of_simple_query runContext clock before connection _ [value] source.site.position
    source.site.table _ source.site.id names original source.site.present
    (originalFilter_calm source.site.source plan.number)
  exact ⟨_, runScriptStep_select_rows rfl rows, runScriptStep_select_rows rfl (same.symm.trans rows)⟩

/-- The signature with one call, the lookup of an id by a value. The call gives the outputs of its
statement. -/
abbrev lookupSignature : Signature Unit where
  Argument _ := Value
  Result _ := List Output

/-- The pairing of the lookup before the expansion with the lookup after it. -/
def Plan.pairing (plan : Plan) : Pairing lookupSignature where
  old := fun _ =>
    { script := originalLookupScript plan.tableName plan.alias plan.idName plan.sourceName plan.text plan.number
      result := id }
  new := fun _ =>
    { script := storedLookupScript plan.tableName plan.alias plan.idName plan.storedName plan.text plan.number
      result := id }

/-- The relation between an old context and a new context. It says: both contexts have the same clock,
and the old connection has the expansion facts, and the database of the new connection is the expanded
database of the old connection. It says nothing about statement indices, output traces, counters, the
snapshot, or the settings of the new connection. -/
def Plan.Related (plan : Plan) (old new : ExecutionContext) : Prop :=
  old.clock = new.clock ∧
    ∃ source : plan.Source old.connection, new.connection.state.database = source.expanded

/-- For every plan: the lookup pairing is a scoped simulation under {name}`Plan.Related`. Plain words:
at every pair of related contexts, the original lookup and the stored lookup give the same rows and the
same value, keep their connections, and lead to related contexts. Proof sketch: the lookups read the
same rows ({name}`Plan.lookup_steps`) and keep their connections, so
{name}`Sql.ScopedAt.of_row_steps` applies, and the relation holds again because it names no part of a
context that a lookup changes. -/
theorem Plan.scoped (plan : Plan) : ScopedSimulation plan.Related plan.pairing := by
  intro name value old new ⟨clock, source, reached⟩
  obtain ⟨rows, oldStep, newStep⟩ := plan.lookup_steps old.clock old.index new.index old.connection
    new.connection source reached value
  rw [clock] at newStep
  exact Sql.ScopedAt.of_row_steps (left := id) (right := id) oldStep newStep rfl ⟨clock, source, reached⟩

/-- The contexts where the expansion of a plan applies: the connection has the expansion facts. -/
def Plan.Admitted (plan : Plan) (state : ExecutionContext) : Prop := Nonempty (plan.Source state.connection)

/-- For every plan: the relation holds between an admitted context and the migrated context of every
returning branch of a successful expansion ({name}`MigrationEntry`). Plain words: after the expansion,
the new context has the expanded database of the old connection and the same clock; its counters are
not related. Proof sketch: {name}`Plan.Source.after_expansion`. -/
theorem Plan.entry (plan : Plan) : MigrationEntry plan.migration plan.Admitted plan.Related := by
  intro state ⟨⟨source⟩, success⟩ run branch _ _
  exact ⟨rfl, source, source.after_expansion success run branch⟩

/-- For every plan, every application over the lookup interface, every admitted context where the
expansion succeeds, and every returning branch of the expansion: the application with the original
lookups, run from the original context, agrees under {name}`Plan.Related` with the application with the
stored lookups, run from the context that the quiet view gives after the expansion branch. Plain words:
both applications give the same value and the same outputs, every raw or concrete choice of one has a
matching choice of the other, and the contexts they reach are related. Later lookups and their values
can depend on earlier results. The statement holds for every database that has a site; the quantifier
over databases is the admitted context. It does not say that the reached contexts are equal. Proof
sketch: {name}`ScopedSimulation.migrated` with {name}`Plan.scoped` and {name}`Plan.entry`. -/
theorem Plan.lookups_agree_after_expansion (plan : Plan) {α : Type} (application : Application lookupSignature α)
    (state : ExecutionContext) (domain : Migration.Domain plan.migration plan.Admitted state)
    (run : SqlRun (List Output))
    (branch : plan.migration.Branch state.clock state.index state.connection run) (value : List Output)
    (returned : run.value = some value) :
    Sql.ScopedAt plan.Related (application.interp plan.pairing.old) (application.interp plan.pairing.new) state
      ((Sql.View.quiet plan.migration).finish state run) :=
  ScopedSimulation.migrated plan.scoped plan.entry application state domain run branch value returned

end Belay.Sqlite.NormalizedFieldExpansion
