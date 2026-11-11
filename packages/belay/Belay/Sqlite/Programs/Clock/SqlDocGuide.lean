import Belay.Sqlite.Frontend.Embedding.DbBang
import Belay.Sqlite.Schema.Rows.DbBang
import Belay.Sqlite.Programs.Claims.SqlDocBlock

set_option doc.verso true

namespace Belay.Sqlite.SqlDoc.Guide

open Belay.Sqlite

/-- A fixed environment for the examples that read the clock. -/
def noon : Env :=
  clockAt "2026-10-20 12:00:00"

/-- The exact outputs of a script that reads NULL and then the text {lit}`NULL`. -/
def nullThenText : List Output :=
  [.rows [[.null]], .rows [["NULL"]]]

end Belay.Sqlite.SqlDoc.Guide
