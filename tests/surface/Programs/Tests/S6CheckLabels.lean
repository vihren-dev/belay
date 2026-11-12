import Belay

/-! A fixture module of `tests/surface_s6_check_programs_test.py`: the command that marks the output of one
{lit}`#sql_check` so that the test can split the output of a module by case (ADR 0017, S6). -/

set_option doc.verso true

open Lean Elab in
/-- Print markers around the messages of one command, so the test can split the output by case. -/
elab "labelled_sql " label:str " in " command:command : command => do
  logInfo m!"SQL-COMMAND-BEGIN {label.getString}"
  Command.elabCommand command
  logInfo m!"SQL-COMMAND-END {label.getString}:"
