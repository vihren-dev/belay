import Belay

/-! Kernel examples of the independent FK atoms, explicit mappings, pragma correspondence and
frames. SQL is parsed by the public surface; proof terms use no native computation. -/

open Belay.Sqlite

set_option doc.verso true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- A matching child whose supporting index precedes the child in the catalog. -/
def indexed : Database := db! r"
  CREATE TABLE p(k TEXT);
  CREATE UNIQUE INDEX p_key ON p(k);
  CREATE TABLE c(x TEXT REFERENCES p(k));
  INSERT INTO p VALUES('a'); INSERT INTO c VALUES('a');"

/-- Explicitly supply the located parent only for the original child position. -/
def supplied : ForeignKeyMapping := ⟨fun child _ =>
  if child == 2 then .located 0 (.columns [(0, 0)]) else .missing⟩

/-- Move the child from position 2 to position 1 after removing the index. -/
def moved : ForeignKeyMapping := ⟨fun child _ =>
  if child == 1 then .located 0 (.columns [(0, 0)]) else .missing⟩

/-- The raw database after dropping catalog position 1. -/
def dropped : Database.Raw := indexed.raw.drop [1]

example : indexed.raw.RowReferencesHold supplied ∧ indexed.raw.ParentSchemasCompatible supplied := by decide +kernel
example : indexed.raw.RowReferencesHold indexed.raw.catalog.foreignKeyMapping := by decide +kernel
example : dropped.RowReferencesHold moved ∧ ¬ dropped.ParentSchemasCompatible moved := by decide +kernel
example : ¬ dropped.RowReferencesHold supplied := by decide +kernel
example : ¬ dropped.RowReferencesHold dropped.catalog.foreignKeyMapping := by decide +kernel
example : dropped.catalog.keyMismatch 1 = some (.foreignKeyMismatch (.ofString "c") (.ofString "p")) := by decide +kernel
example : (indexed.run (sql "PRAGMA foreign_keys=ON; DROP INDEX p_key; PRAGMA foreign_key_check;")).outputs =
    [.done 0, .done 0, .error 1] := by decide +kernel

/-- A caller that supplies no comparisons still checks every declaration. -/
def omitted : ForeignKeyMapping := ⟨fun _ _ => .missing⟩
example : ¬ indexed.raw.RowReferencesHold omitted ∧ ¬ indexed.raw.ParentSchemasCompatible omitted := by decide +kernel

/-- A raw child with no target, whose NULL key vacuously satisfies row references. -/
def absent : Database := db! "CREATE TABLE c(x REFERENCES p); INSERT INTO c VALUES(NULL);"
example : absent.raw.RowReferencesHold absent.raw.catalog.foreignKeyMapping ∧
    ¬ absent.raw.ParentSchemasCompatible absent.raw.catalog.foreignKeyMapping := by decide +kernel
example : absent.raw.catalog.keyMismatch 0 = none := by decide +kernel
example : (absent.run (sql "PRAGMA foreign_key_check")).outputs = [.rows []] := by decide +kernel

/-- A present parent without a unique key fails schema compatibility even with no child rows. -/
def nonunique : Database := db! "CREATE TABLE p(k); CREATE TABLE c(x REFERENCES p(k));"
example : nonunique.raw.RowReferencesHold nonunique.raw.catalog.foreignKeyMapping ∧
    ¬ nonunique.raw.ParentSchemasCompatible nonunique.raw.catalog.foreignKeyMapping := by decide +kernel
example : (nonunique.run (sql "PRAGMA foreign_key_check")).outputs = [.error 1] := by decide +kernel

/-- A missing target with a non-NULL key violates row references as well as compatibility. -/
def missingOrphan : Database := db! "CREATE TABLE c(x REFERENCES p); INSERT INTO c VALUES(9);"
example : ¬ missingOrphan.raw.RowReferencesHold missingOrphan.raw.catalog.foreignKeyMapping ∧
    ¬ missingOrphan.raw.ParentSchemasCompatible missingOrphan.raw.catalog.foreignKeyMapping := by decide +kernel

/-- A schema-compatible orphan is possible when enforcement is off. -/
def orphan : Database := db! "CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p); INSERT INTO c VALUES(9);"
example : orphan.raw.ParentSchemasCompatible orphan.raw.catalog.foreignKeyMapping ∧
    ¬ orphan.raw.RowReferencesHold orphan.raw.catalog.foreignKeyMapping := by decide +kernel

/-- Repeated parent columns select child x twice, preserving the supported non-NULL case. -/
def repeated : Database := db! r"
  CREATE TABLE p(a,b,PRIMARY KEY(a,a));
  CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b));
  PRAGMA foreign_keys=ON;
  INSERT INTO p VALUES(1,2); INSERT INTO c VALUES(1,99);"
example : repeated.raw.ParentSchemasCompatible repeated.raw.catalog.foreignKeyMapping ∧
    repeated.raw.RowReferencesHold repeated.raw.catalog.foreignKeyMapping := by decide +kernel
example : (repeated.run (sql "PRAGMA foreign_key_check")).outputs = [.rows []] := by decide +kernel

/-- An unused declaration column is NULL while the selected child x has no parent. -/
def unusedNull : Database := db! r"
  CREATE TABLE p(a,b,PRIMARY KEY(a,a));
  CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b));
  INSERT INTO p VALUES(1,2); INSERT INTO c VALUES(99,NULL);"
example : unusedNull.raw.ParentSchemasCompatible unusedNull.raw.catalog.foreignKeyMapping ∧
    ¬ unusedNull.raw.RowReferencesHold unusedNull.raw.catalog.foreignKeyMapping := by decide +kernel

/-- NULL in selected child x exempts the repeated comparison even without any parent rows. -/
def selectedNull : Database := db! r"
  CREATE TABLE p(a,b,PRIMARY KEY(a,a));
  CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b));
  PRAGMA foreign_keys=ON; INSERT INTO c VALUES(NULL,99);"
example : selectedNull.raw.RowReferencesHold selectedNull.raw.catalog.foreignKeyMapping := by decide +kernel

/-- Different parent lookup and scan affinities permit this enforced trigger write to leave an orphan. -/
def affinityOrphan : Database := db! r"
  PRAGMA foreign_keys=ON;
  CREATE TABLE p(k TEXT UNIQUE); CREATE TABLE c(x INTEGER REFERENCES p(k));
  INSERT INTO p VALUES('1'); INSERT INTO c VALUES(1);
  CREATE TRIGGER replace_parent AFTER DELETE ON p WHEN old.k='1'
    BEGIN INSERT INTO p VALUES('01'); END;
  DELETE FROM p WHERE k='1';"
example : affinityOrphan.raw.ParentSchemasCompatible affinityOrphan.raw.catalog.foreignKeyMapping ∧
    ¬ affinityOrphan.raw.RowReferencesHold affinityOrphan.raw.catalog.foreignKeyMapping := by decide +kernel

/-- Without a located comparison, either declaration column can supply the NULL exemption. -/
def missingComposite : Database := db! r"
  CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b)); INSERT INTO c VALUES(99,NULL);"
example : missingComposite.raw.RowReferencesHold missingComposite.raw.catalog.foreignKeyMapping ∧
    ¬ missingComposite.raw.ParentSchemasCompatible missingComposite.raw.catalog.foreignKeyMapping := by decide +kernel

/-- Parent affinity and NOCASE apply to the supplied comparison exactly as in engine checks. -/
def affinity : Database := db! r"
  CREATE TABLE p(a INTEGER, b TEXT COLLATE NOCASE, PRIMARY KEY(a,b));
  CREATE TABLE c(x TEXT,y TEXT,FOREIGN KEY(x,y) REFERENCES p);
  INSERT INTO p VALUES(1,'A'); INSERT INTO c VALUES('01','a');"
example : affinity.raw.RowReferencesHold affinity.raw.catalog.foreignKeyMapping ∧
    affinity.raw.ParentSchemasCompatible affinity.raw.catalog.foreignKeyMapping := by decide +kernel

/-- INTEGER PRIMARY KEY uses integer rowid matching after numeric affinity. -/
def rowid : Database := db! r"
  CREATE TABLE p(k INTEGER PRIMARY KEY); CREATE TABLE c(x REFERENCES p);
  INSERT INTO p VALUES(1); INSERT INTO c VALUES('01');"
example : rowid.raw.RowReferencesHold rowid.raw.catalog.foreignKeyMapping := by decide +kernel

/-- Each unsupported parent shape is checked with no child rows or only a NULL key.
The nonunique-parent case stores the NULL key. -/
def unsupportedParents : List Database := [
  db! "CREATE TABLE p(k); CREATE UNIQUE INDEX pk ON p(k) WHERE k>0; CREATE TABLE c(x REFERENCES p(k));",
  db! "CREATE TABLE p(k); CREATE UNIQUE INDEX pk ON p(k+0); CREATE TABLE c(x REFERENCES p(k));",
  db! "CREATE TABLE p(k TEXT); CREATE UNIQUE INDEX pk ON p(k COLLATE NOCASE); CREATE TABLE c(x REFERENCES p(k));",
  db! "CREATE TABLE p(a,b,PRIMARY KEY(a,b)); CREATE TABLE c(x REFERENCES p);",
  db! "CREATE TABLE p(k); CREATE TABLE c(x REFERENCES p(k)); INSERT INTO c VALUES(NULL);"
]
example : unsupportedParents.all (fun db =>
    !db.raw.parentSchemasCompatible db.raw.catalog.foreignKeyMapping &&
      db.raw.rowReferencesHold db.raw.catalog.foreignKeyMapping) = true := by decide +kernel

/-- The exported full-statement theorem establishes the pragma output from both new facts. -/
theorem selectedPragmaEmpty :
    (Belay.Sqlite.Model.runScriptStep runContext none 0 (repeated.raw.connection {})
      (.pragma (.foreignKeyCheck none)) []).output = .rows [] := by
  apply (Belay.Sqlite.Model.runScriptStep_keyCheck_empty _ _ _ _ _ (fun position _ =>
    Belay.Sqlite.Model.Database.ParentSchemasCompatible.noMismatch
      (by decide +kernel : repeated.raw.ParentSchemasCompatible repeated.raw.catalog.foreignKeyMapping) position)).mpr
  decide +kernel

/-- A caller may use one explicit comparison for every declaration of this database. -/
def sameParent : ForeignKeyMapping := ⟨fun _ _ => .located 0 (.columns [(0, 0)])⟩

/-- The drop law carries an explicit mapping through the index removal; it does not assume
that the result already has the row fact or that the supporting index still exists. -/
theorem dropPreservesRows : dropped.RowReferencesHold sameParent := by
  apply Belay.Sqlite.Model.Database.RowReferencesHold.drop
    (database := indexed.raw) (mapping := sameParent) (by decide +kernel) [1] sameParent
  · intro child table present key declared
    rfl
  · intro child table present key declared parent comparison selected
    cases selected
    decide

/-- Deleting the parent's rows with enforcement off changes row truth but keeps the schema. -/
def parentDeleted : Database.Raw := indexed.raw.setRows 0 []

/-- Removing these parent rows keeps schema compatibility because the catalog is unchanged. -/
theorem parentDeleteKeepsSchema : parentDeleted.ParentSchemasCompatible sameParent :=
  Belay.Sqlite.Model.Database.ParentSchemasCompatible.catalog_eq
    (before := indexed.raw) (by decide +kernel) rfl

example : ¬ parentDeleted.RowReferencesHold sameParent := by decide +kernel

/-- The second index remains eligible, but selecting its reversed column order changes mappings. -/
def twoIndexes : Database := db! r"
  CREATE TABLE p(a,b); CREATE UNIQUE INDEX first_key ON p(a,b);
  CREATE UNIQUE INDEX second_key ON p(b,a);
  CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b));
  INSERT INTO p VALUES(1,2); INSERT INTO c VALUES(1,2);"

/-- The catalog after removing the first eligible parent index. -/
def secondSelected : Database.Raw := twoIndexes.raw.drop [1]
/-- Retain the original parent choice while the catalog selects another choice. -/
def priorMapping : ForeignKeyMapping := twoIndexes.raw.catalog.foreignKeyMapping
example : secondSelected.RowReferencesHold priorMapping ∧
    ¬ secondSelected.ParentSchemasCompatible priorMapping := by decide +kernel
example : secondSelected.ParentSchemasCompatible secondSelected.catalog.foreignKeyMapping := by decide +kernel

#print axioms selectedPragmaEmpty
#print axioms Belay.Sqlite.Model.ForeignKeyMapping.selected_satisfied
#print axioms Belay.Sqlite.Model.Table.rowReferencesHold_selected_iff
#print axioms Belay.Sqlite.Model.Database.rowReferencesHold_iff
#print axioms Belay.Sqlite.Model.Database.parentSchemasCompatible_iff
#print axioms Belay.Sqlite.Model.Database.RowReferencesHold.frame
#print axioms Belay.Sqlite.Model.Database.ParentSchemasCompatible.frame
#print axioms Belay.Sqlite.Model.Database.RowReferencesHold.drop
#print axioms Belay.Sqlite.Model.resolvePragma_keyCheck_iff
#print axioms Belay.Sqlite.Model.Database.ParentSchemasCompatible.noMismatch

#print axioms dropPreservesRows
#print axioms parentDeleteKeepsSchema
#print axioms Belay.Sqlite.Model.runScriptStep_keyCheck_empty
#print axioms Belay.Sqlite.Model.runScriptStep_tableKeyCheck_empty
