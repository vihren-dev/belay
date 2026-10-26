import Belay.Sqlite.Model.ForeignKeyCounterWrites

/-! Every new row-engine preservation theorem uses only the standard logical axioms. -/

#print axioms Belay.Sqlite.Model.admittedWriteLaws
#print axioms Belay.Sqlite.Model.WriteLaws.and
#print axioms Belay.Sqlite.Model.ResultHolds.and
#print axioms Belay.Sqlite.Model.ResultHolds.with_eq
#print axioms Belay.Sqlite.Model.ResultHolds.foldlM_mem
#print axioms Belay.Sqlite.Model.KeyState.table_aligned
#print axioms Belay.Sqlite.Model.KeyState.foundRow_table
#print axioms Belay.Sqlite.Model.KeyState.foreignKeyInvariant_of_rows_counter
#print axioms Belay.Sqlite.Model.runPrograms_empty
#print axioms Belay.Sqlite.Model.RowChange.Covers.assignFrom
#print axioms Belay.Sqlite.Model.RowChange.Covers.of_setCells
#print axioms Belay.Sqlite.Model.deleteRow_counterBound
#print axioms Belay.Sqlite.Model.updateChecks_covered_bound
#print axioms Belay.Sqlite.Model.updateRow_counterBound
#print axioms Belay.Sqlite.Model.insertWrite_counterBound
#print axioms Belay.Sqlite.Model.failedRow_foreignKeyInvariant
#print axioms Belay.Sqlite.Model.insertRow_counterBound
#print axioms Belay.Sqlite.Model.ForeignKeyUpdateConditions.assignFrom
#print axioms Belay.Sqlite.Model.raiseEffect_foreignKeyInvariant
#print axioms Belay.Sqlite.Model.runStep_counterBound
#print axioms Belay.Sqlite.Model.enterProgram_counterBound
#print axioms Belay.Sqlite.Model.runProgram_counterBound
#print axioms Belay.Sqlite.Model.runPrograms_counterBound
#print axioms Belay.Sqlite.Model.KeyResult.mapState_foreignKeyInvariant
#print axioms Belay.Sqlite.Model.NestedRun.credited_foreignKeyKeeps
#print axioms Belay.Sqlite.Model.runAction_foreignKeyInvariant
#print axioms Belay.Sqlite.Model.deleteRow_nested_counter
#print axioms Belay.Sqlite.Model.replaceDelete_nested_counter
#print axioms Belay.Sqlite.Model.updateRow_nested_counter
#print axioms Belay.Sqlite.Model.insertRow_nested_counter
#print axioms Belay.Sqlite.Model.runRows_foreignKeyKeeps
#print axioms Belay.Sqlite.Model.NestedRun.beforeUpdateFrame_of_empty
#print axioms Belay.Sqlite.Model.rowsKeys_rowReferences
