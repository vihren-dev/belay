"""The native record versions and what each one carries (docs/conformance-format-v2.md).

Version 1 is a migration trace; version 2 adds setup operations; version 3 adds
statement outputs; version 4 adds an explicit execution profile; version 5 has a
profile with measured limits (format 3) and the error phase of each event. Readers
ask these sets instead of comparing version numbers, so a new version changes one
place.
"""

WITH_OUTPUTS = (3, 4, 5)
"""Versions whose trace events carry statement outputs and bound parameters."""
PROFILED = (4, 5)
"""Versions with an explicit `profile` record."""
PHASED = (5,)
"""Versions whose trace events carry the error `phase`."""
