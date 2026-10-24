import ViewsSupport

set_option doc.verso true
set_option maxRecDepth 8000
set_option maxHeartbeats 800000

/-! Stored definitions hide caller SQL names but keep the indexed cell layout.
Exact messages distinguish native preparation errors from model restrictions. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open ViewExamples

namespace ViewScopeExamples

/-- Invalid and circular bodies remain legal unresolved catalog definitions. -/
def database : Database := ⟨withViews base [
  (name! "closed", definition (sql r"SELECT outer_source.x")),
  (name! "bare", definition (sql r"SELECT x")),
  (name! "alias_filter", definition (sql r"SELECT 1 WHERE x=100")),
  (name! "bare_rowid", definition (sql r"SELECT rowid")),
  (name! "outer_star", definition (sql r"SELECT outer_source.*")),
  (name! "new_row", definition (sql r"SELECT new.x")),
  (name! "old_row", definition (sql r"SELECT old.x")),
  (name! "duplicates", definition (sql r"SELECT 1,2") (some [name! "x",name! "x"])),
  (name! "Camel", definition (sql r"SELECT 1") (some [name! "a", name! "b"])),
  (name! "bad_count", definition (sql r"SELECT missing") (some [name! "a", name! "b"])),
  (name! "cycle", definition (sql r"SELECT * FROM Cycle")),
  (name! "indirect", definition (sql r"SELECT * FROM cycle")),
  (name! "system_source", definition (sql r"SELECT * FROM sqlite_schema")),
  (name! "implicit_rowid", definition (sql r"SELECT rowid FROM t")),
  (name! "v", definition (sql r"SELECT x FROM t"))], by decide +kernel⟩

/-- Ordinary outer qualifiers are invisible inside a stored body. -/
example : prepareMessage (sql r"SELECT (SELECT * FROM closed) FROM t outer_source") database =
    some "no such column: outer_source.x" := by decide +kernel

/-- An unqualified name cannot read a caller source, either. -/
example : prepareMessage (sql r"SELECT (SELECT * FROM bare) FROM t") database =
    some "no such column: x" := by decide +kernel

/-- A stored WHERE cannot read a caller result alias or inherit its alias restriction. -/
example : prepareMessage (sql r"SELECT 100 AS x WHERE EXISTS(SELECT * FROM alias_filter)") database =
    some "no such column: x" := by decide +kernel

/-- Hidden caller rowid sources do not turn a missing name into a rowid restriction. -/
example : prepareMessage (sql r"SELECT (SELECT * FROM bare_rowid) FROM t") database =
    some "no such column: rowid" := by decide +kernel

/-- A qualifier hidden at view entry cannot supply a source star. -/
example : prepareMessage (sql r"SELECT (SELECT * FROM outer_star) FROM t outer_source") database =
    some "no such table: outer_source" := by decide +kernel

/-- A stored NEW reference needs a trigger context. -/
example : prepareMessage (sql r"SELECT * FROM new_row") database =
    some "no such column: new.x" := by decide +kernel

/-- A stored OLD reference also needs a trigger context. -/
example : prepareMessage (sql r"SELECT * FROM old_row") database =
    some "no such column: old.x" := by decide +kernel

/-- The declared view spelling appears in the column-count error. -/
example : prepareMessage (sql r"SELECT * FROM cAMEL") database =
    some "expected 2 columns for 'Camel' but got 1" := by decide +kernel

/-- Duplicate explicit names reuse the existing derived-name disambiguation. -/
example : Holds (sql r"SELECT 1 FROM duplicates WHERE x=1 AND [x:1]=2") database := by decide +kernel

/-- Body name resolution precedes the explicit column-count mismatch. -/
example : prepareMessage (sql r"SELECT * FROM bad_count") database =
    some "no such column: missing" := by decide +kernel

/-- A direct cycle reports the catalog spelling, independent of its use spelling. -/
example : prepareMessage (sql r"SELECT * FROM CYCLE") database =
    some "view cycle is circularly defined" := by decide +kernel

/-- A caller CTE does not hide a genuine cycle in a stored definition. -/
example : prepareMessage (sql r"WITH cycle AS (SELECT 100) SELECT * FROM indirect") database =
    some "view cycle is circularly defined" := by decide +kernel

/-- Function syntax is rejected before the circular body is expanded. -/
example : prepareMessage (sql r"SELECT * FROM cycle()") database =
    some "'cycle' is not a function" := by decide +kernel

/-- Function syntax also precedes an independent missing-column body error. -/
example : prepareMessage (sql r"SELECT * FROM bad_count()") database =
    some "'bad_count' is not a function" := by decide +kernel

/-- A restriction during stored-source expansion points at this statement's use. -/
example : restriction (sql r"SELECT * FROM system_source") database =
    some ⟨[1], .systemTable⟩ := by decide +kernel

/-- A restriction during later body resolution also points at the view use. -/
example : restriction (sql r"SELECT * FROM implicit_rowid") database =
    some ⟨[1], .rowidName⟩ := by decide +kernel

/-- A correlated scalar query retains its ordinary outer lookup. -/
example : Holds (sql r"SELECT 1 FROM (SELECT 100 AS x) WHERE (SELECT x+1)=101") database := by decide +kernel

/-- An ordinary nested WHERE retains the existing result-alias restriction. -/
example : restriction (sql r"SELECT 100 AS x WHERE EXISTS(SELECT 1 WHERE x=100)") database =
    some ⟨[8, 0, 3], .aliasInExpression⟩ := by decide +kernel

/-- A derived source sees the enclosing x, not its sibling's x or cells. -/
example : Holds (sql r"SELECT 1 FROM (SELECT 7 AS x)
    WHERE (SELECT z FROM (SELECT x AS z) d,(SELECT 900 AS x) sibling)=7") database := by decide +kernel

/-- A closed view reached through a scalar query ignores excess caller cells. -/
example : Holds (sql r"SELECT 1 FROM (SELECT 100 AS x)
    WHERE (SELECT x FROM v WHERE x=7)=7") database := by decide +kernel

end ViewScopeExamples
