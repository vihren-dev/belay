import Belay
import Belay.Sqlite.SqlDocCheck

set_option doc.verso true

namespace SqlDocObservation
open Belay.Sqlite Belay.Sqlite.SqlDoc

-- Text observations omit write counts and preserve row and statement order.
#guard (checkOutputs (.text "1 | two\n3") [.done 2, .rows [[1, "two"]], .rows [], .rows [[3]]]).isOk
#guard (checkOutputs (.text "") [.done 7, .rows []]).isOk
#guard (checkOutputs (.text "") []).isOk
#guard (checkOutputs (.text "1\n2") [.rows [[1]], .rows [[2]]]).isOk
#guard !(checkOutputs (.text "2\n1") [.rows [[1]], .rows [[2]]]).isOk

-- The cell renderer preserves bytes, spaces and embedded/empty lines.
#guard (checkOutputs (.text "NULL | x'00ff' | text x'ff'")
  [.rows [[.null, .blob [0, 255], .text [255]]]]).isOk
#guard (checkOutputs (.text " left  | a\nb\n") [.rows [[" left ", "a\nb"], [""]]]).isOk
#guard !(checkOutputs (.text "left") [.rows [[" left "]]]).isOk
#guard (checkOutputs (.text "\n1") [.rows [[]], .rows [[1]]]).isOk
#guard (checkOutputs (.text "1") [.rows [], .rows [[1]]]).isOk

-- Typed observations distinguish collisions in text, boundaries and write counts.
#guard (checkOutputs (.text "NULL") [.rows [[.null]]]).isOk
#guard (checkOutputs (.text "NULL") [.rows [["NULL"]]]).isOk
#guard !(checkOutputs (.outputs [.rows [[.null]]]) [.rows [["NULL"]]]).isOk
#guard !(checkOutputs (.outputs [.rows [[1], [2]]]) [.rows [[1]], .rows [[2]]]).isOk
#guard !(checkOutputs (.outputs []) [.rows []]).isOk
#guard !(checkOutputs (.outputs [.done 0]) [.done 1]).isOk
#guard (checkOutputs (.outputs [.done 1, .rows [[.null]]]) [.done 1, .rows [[.null]]]).isOk

-- Every choice contributes; equal displays can have different storage classes.
#guard (checkOutputs (.text "NULL\n1")
  [.oneOf [[[.null]], [["NULL"]]], .oneOf [[[1]], [["1"]]]]).isOk
#guard !(checkOutputs (.text "1\n2")
  [.oneOf [[[1]], [[1]]], .oneOf [[[2]], [[3]]]]).isOk
#guard !(checkOutputs (.text "1") [.oneOf [[[1]], [[2]]]]).isOk
#guard (checkOutputs (.outputs [.oneOf [[[1]], [[2]]]]) [.oneOf [[[1]], [[2]]]]).isOk
#guard !(checkOutputs (.outputs [.rows [[1]]]) [.oneOf [[[1]], [[2]]]]).isOk

-- Neither normal mode can bless an error, restriction or vacuous alternatives list.
#guard !(checkOutputs (.text "") [.oneOf []]).isOk
#guard !(checkOutputs (.outputs [.oneOf []]) [.oneOf []]).isOk
#guard !(checkOutputs (.text "") [.error 19]).isOk
#guard !(checkOutputs (.outputs [.error 19]) [.error 19]).isOk
#guard !(checkOutputs (.text "") [.unmodeled "clock unavailable"]).isOk
#guard !(checkOutputs (.outputs [.unmodeled "clock unavailable"]) [.unmodeled "clock unavailable"]).isOk
#guard match checkOutputs (.text "") [.done 0, .error 19, .unmodeled "later"] with
  | .error (.sqlError 1 19) => true
  | _ => false

/-- A closed starting database that lets the adapter exercise a real write and read. -/
def start : Database := db! r"CREATE TABLE t(x INTEGER); INSERT INTO t VALUES(1)"

#guard (check start Env.default (sql r"UPDATE t SET x = 7; SELECT x FROM t") (.text "7")).isOk
#guard (check start Env.default (sql r"SELECT x FROM t") (.text "1")).isOk
#guard (check start Env.default (sql r"SELECT x FROM t WHERE x = 0") (.outputs [.rows []])).isOk
#guard !(check start Env.default (sql r"SELECT x FROM t WHERE x = 0") (.text "1")).isOk
#guard (check start Env.default (sql r"SELECT ?1" 9) (.text "9")).isOk
#guard !(check start Env.default (sql r"SELECT CURRENT_TIMESTAMP") (.text "")).isOk
#guard (check start (clockAt "2026-10-24 00:00:00") (sql r"SELECT CURRENT_TIMESTAMP")
  (.text "2026-10-24 00:00:00")).isOk
#guard !(check start Env.default (sql r"SELECT absent FROM t") (.text "")).isOk

#eval IO.println "SQL doc observation checks passed"
end SqlDocObservation
