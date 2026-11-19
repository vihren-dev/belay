# Success of a literal INSERT at a script step

Created 2026-11-19. Open. [Issue 419](https://github.com/vihren-dev/belay/issues/419).

A plain INSERT of literal rows with a found target and fitting values
succeeds in one execution. The run is ready, its change count is the
number of rows inserted, and its effect stores the inserted rows at the
target. With a known clock and known counters, the script step continues
with the corresponding done output and updated connection. This law covers
ordinary inserts without RETURNING, conflict handling, triggers or enforced
foreign-key rules.

A separate bridge from database validity must establish InsertFits from
conditions on the new values and keys. The condition on multiple new rows
is pending owner clarification. Keys of two new rows may conflict even
when the original table was empty.

## Acceptance

Compile the statement and step laws for arbitrary literal rows. Apply the
step law to an insert of two rows and check its output, updated counters
and stored rows. Keep a duplicate-key counterexample, including two equal
keys in one insert on an empty table. The proof audit accepts only the
usual logical axioms. Complete the validity bridge against the agreed
key premise before claiming this issue is done.

InsertFits is in Schema/Writes/InsertSelectSuccess.lean. StatementRun
defines insertOutcome. Programs/Scripts/InsertSelectStepLaws.lean already
connects an ordinary INSERT from a query to the script-step result.
