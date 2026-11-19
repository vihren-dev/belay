# Status of execution guards for resolved schema statements

Created 2026-11-19. DONE. [Task](20261119-resolved-step-guards.task.md).

At the start of the task the revision was `c8ff959b`. In `Schema/Dispatch/ResolveStatementForms.lean`,
`SchemaLink` required only the strict default fact for ADD COLUMN and closure
of positions for DROP. In `Programs/Scripts/StepContinuesOk.lean` and
`Programs/Scripts/SchemaStepRules.lean`, CREATE TABLE and rewrite took
explicit guards. In `Programs/Scripts/SchemaSuccess.lean` the Boolean check
evaluated both. The rebuild example already used the certified
schema path and contained neither of the two rename helpers named in the issue.

Resolution now records the positions of new catalog objects, the bounds on the
table of ADD COLUMN and CREATE INDEX, the drop-column check and the catalog
of the rewrite. ResolvedStepGuards derives the execution guards from this
link and a valid connection. The surface rules for CREATE TABLE and rename
use these laws. SchemaRuleExamples exercises both rules on abstract initial
connections. The affected tests are tests/test_model_package.py and
tests/surface_rebuild_test.py. Review found a catch-all case in StepGuards. The match now lists each
statement kind so a new kind needs an explicit decision. Corrected the proof
sketches to name the direct step theorem.

The second code review found no issues. The Nix full test suite and the Nix
verdict passed for this change. The first full run exceeded the frozen v5
progress timeout. The isolated rerun passed all 153 tests, and the full
rerun passed. The timeout is tracked in issue 454.

The combined stack passed all 99 Nix host tests and the scheduled checks.
