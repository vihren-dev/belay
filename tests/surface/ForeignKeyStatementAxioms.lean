import Belay.Sqlite.Model.ForeignKeyRuns

/-! Audit every new statement/run bridge and outside-footprint theorem for forbidden axioms. -/

#print axioms Belay.Sqlite.Model.Database.foreignKeyViolations_setRows_outside
#print axioms Belay.Sqlite.Model.Database.RowReferencesHold.rowsOnlyAt
#print axioms Belay.Sqlite.Model.ForeignKeyAssignmentConditions.work
#print axioms Belay.Sqlite.Model.runStatement_rowReferences
#print axioms Belay.Sqlite.Model.rowReferences_statementKeeps
#print axioms Belay.Sqlite.Model.runSqlFrom_rowReferences
#print axioms Belay.Sqlite.Model.runSql_rowReferences
#print axioms Belay.Sqlite.Model.runScriptFrom_rowReferences
#print axioms Belay.Sqlite.Model.Database.ParentSchemasCompatible.rowReferences_iff_selected
#print axioms Belay.Sqlite.Model.foreignKeyAtoms_statementKeeps
#print axioms Belay.Sqlite.Model.runStatement_foreignKeyAtoms
#print axioms Belay.Sqlite.Model.runSqlFrom_foreignKeyAtoms
#print axioms Belay.Sqlite.Model.runSql_foreignKeyAtoms
#print axioms Belay.Sqlite.Model.runScriptFrom_foreignKeyAtoms
