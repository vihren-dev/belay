import Belay.Sqlite.Model.ForeignKeyRuns

/-! Audit generic run lifting, independent foreign-key evidence and outside-footprint facts. -/

#print axioms Belay.Sqlite.Model.Database.foreignKeyViolations_setRows_outside
#print axioms Belay.Sqlite.Model.Database.RowReferencesHold.rowsOnlyAt
#print axioms Belay.Sqlite.Model.ForeignKeyAssignmentConditions.work
#print axioms Belay.Sqlite.Model.runStatement_rowReferences
#print axioms Belay.Sqlite.Model.rowReferences_statementKeeps
#print axioms Belay.Sqlite.Model.Database.ParentSchemasCompatible.rowReferences_iff_selected
#print axioms Belay.Sqlite.Model.foreignKeyAtoms_statementKeeps
#print axioms Belay.Sqlite.Model.runStatement_foreignKeyAtoms

#print axioms Belay.Sqlite.Model.runSqlFrom_holds
#print axioms Belay.Sqlite.Model.runSql_holds
#print axioms Belay.Sqlite.Model.runScriptAllFrom_holds
