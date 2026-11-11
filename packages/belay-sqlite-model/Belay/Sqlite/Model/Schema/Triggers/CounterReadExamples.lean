import Belay.Sqlite.Model.Schema.Dispatch.CounterReadExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.CounterReadExamples

open Belay.Sqlite.Model Syntax

open TriggerRunExamples in
/-- A read of a counter in a trigger program, in the body or in the {lit}`WHEN` condition, is the
restriction of a trigger form at the write that runs the program. -/
example : restrictionOf (tables ++ [trigger "a" .after .insert [logged (.call "changes" [])], insertT [[.null, .numeric "7"]]]) =
    some .triggerForm := by decide +kernel
open TriggerRunExamples in
example : restrictionOf (tables ++ [trigger "a" .after .insert [selected (.call "total_changes" [])],
    insertT [[.null, .numeric "7"]]]) = some .triggerForm := by decide +kernel
open TriggerRunExamples in
example : restrictionOf (tables ++ [trigger "a" .after .insert [logged (.numeric "1")]
    (some (.compare .eq (.call "last_insert_rowid" []) (.numeric "1"))), insertT [[.null, .numeric "7"]]]) =
    some .triggerForm := by decide +kernel

open TriggerRunExamples in
/-- A trigger whose body reads a counter and that no statement fires is no restriction: the
restriction comes at the write that runs the program. -/
example : restrictionOf (tables ++ [trigger "a" .after .insert [logged (.call "changes" [])]]) = none := by
  decide +kernel

open TriggerRunExamples in
/-- {lit}`total_changes()` in a write that runs a trigger program is a restriction. -/
example : restrictionOf (tables ++ [trigger "a" .after .insert [logged (.numeric "1")],
    insertT [[.null, .call "total_changes" []]]]) = some .connectionCounterRead := by decide +kernel

end Belay.Sqlite.Model.CounterReadExamples
