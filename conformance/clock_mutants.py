"""Mutants of the clock (ADR 0012, amendment 5, slice 6e2).

The task of slice 6e2 lists the changes that the conformance suite must notice. Each
mutant is one text change in a copy of the model, which
`conformance.resolve_mutants.measure` builds and runs against its target case of
`conformance.authored_clock`.
"""

from conformance.resolve_mutants import SQLITE

EXECUTION = SQLITE + "SqlExecution.lean"
"""The clock assignment with which a script runs."""
FUNCTIONS = SQLITE + "Date/Functions.lean"
"""The date and time functions, which give the time keywords their text."""
STATEMENT = SQLITE + "StatementClock.lean"
"""The cells of INSERT rows at a clock value."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "clock_one_for_script": (EXECUTION,
        "  if (script[position]?).any Resolved.Statement.readsClock then clock position else 0",
        "  if (script[position]?).any Resolved.Statement.readsClock then clock 0 else 0"),
    "clock_date_with_time": (FUNCTIONS, "      | .date => .text x.computeCivilDate.dateText",
        "      | .date => .text (x.computeCivilDate.computeTimeOfDay.dateText ++ [32] ++\n"
        "          x.computeCivilDate.computeTimeOfDay.timeText)"),
    "clock_seconds_rounded": (FUNCTIONS, "    else twoDigitBytes (doubleToInt32 x.seconds)",
        "    else twoDigitBytes (doubleToInt32 (x.seconds + 0.5))"),
    "clock_default_at_resolution": (STATEMENT,
        "  | .expression term => storeValue affinity (term.eval clock [])",
        "  | .expression term => storeValue affinity (term.eval defaultDateClock [])"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the replacement. The
names follow the list in the task of slice 6e2: one clock value, the first statement's, for
all statements of a script; `CURRENT_DATE` with the time; seconds rounded instead of
truncated; the cells of an INSERT, such as an omitted value with a time default, at one
clock value fixed before the script runs (`defaultDateClock`), as if resolution evaluated
them, instead of the clock value of their statement."""

TARGETS: dict[str, tuple[str, ...]] = {
    "clock_one_for_script": ("clock-per-statement",), "clock_date_with_time": ("clock-keywords-fromless",),
    "clock_seconds_rounded": ("clock-keywords-fromless",), "clock_default_at_resolution": ("clock-default-affinity",),
}
"""The authored case of `conformance.authored_clock` that each mutant changes."""

GUARDS: dict[str, str] = {
    "clock_one_for_script": "rule:scriptClock", "clock_date_with_time": "rule:Resolved.DateFunction.value",
    "clock_seconds_rounded": "rule:DateTime.timeText", "clock_default_at_resolution": "rule:Cell.valueAt",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
