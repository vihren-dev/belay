import Belay.Sqlite.QueryEval

set_option doc.verso true

/-! Checked examples of the aggregates {lit}`group_concat`, {lit}`string_agg` and {lit}`total`
(ADR 0015, slice 5) over groups of evaluated rows. Each result was checked on native SQLite
3.51.0, one statement per line. -/

namespace Belay.Sqlite.Resolved.AggregateExamples

open Belay.Sqlite

/-- The TEXT value of a string. -/
def text (string : String) : Value := .text string.toUTF8.toList

/-- Rows of one group: a value and a separator per row. -/
def rows : List (List Value) :=
  [[text "b", text "-"], [.real (2.5 : Float).toBits, text "+"], [.null, text "*"], [text "", text ";"],
   [.blob [0x41, 0x42], .null], [.integer 7, text "/"]]

-- group_concat(v): a comma between values, NULL skipped, an empty value kept, a BLOB as its bytes.
#guard (Aggregate.groupConcat (.column 0) none).eval 0 rows == text "b,2.5,,AB,7"
-- group_concat(v, s): the separator of each later value's own row; nothing for a NULL one.
#guard (Aggregate.groupConcat (.column 0) (some (.column 1))).eval 0 rows == text "b+2.5;AB/7"
-- NULL for an empty group or one where every value is NULL; '' for one empty value.
#guard (Aggregate.groupConcat (.column 0) none).eval 0 [] == .null
#guard (Aggregate.groupConcat (.column 0) none).eval 0 [[.null]] == .null
#guard (Aggregate.groupConcat (.column 0) none).eval 0 [[text ""]] == text ""
-- total: a REAL, 0.0 for an empty group, and no overflow.
#guard (Aggregate.total (.column 0)).eval 0 [] == .real (0.0 : Float).toBits
#guard (Aggregate.total (.column 0)).eval 0 [[.integer 9223372036854775807], [.integer 1], [.integer (-5)]] ==
  .real (9223372036854775807.0 : Float).toBits
#guard !(Aggregate.total (.column 0)).fails 0 [[.integer 9223372036854775807], [.integer 1]]

example : (Aggregate.groupConcat (.column 0) (some (.column 1))).eval 0 [[text "a", text "x"], [text "b", text "y"]] =
    text "ayb" := by
  decide +kernel

end Belay.Sqlite.Resolved.AggregateExamples
