# Status of execution guards for resolved schema statements

Created 2026-11-19. Open. [Task](20261119-resolved-step-guards.task.md).

The starting revision is `c8ff959b`. In `Schema/Dispatch/ResolveStatementForms.lean`,
`SchemaLink` requires only the strict default fact for ADD COLUMN and closure
of positions for DROP. In `Programs/Scripts/StepContinuesOk.lean` and
`Programs/Scripts/SchemaStepRules.lean`, CREATE TABLE and rewrite still take
explicit guards. In `Programs/Scripts/SchemaSuccess.lean` the Boolean check
still evaluates both. The current rebuild example already uses the certified
schema path and contains neither of the two rename helpers named in the issue.

Resolution now records the positions of new catalog objects, the bounds on the
table of ADD COLUMN and CREATE INDEX, the drop-column check and the catalog
of the rewrite. ResolvedStepGuards derives the execution guards from this
link and a valid connection. The surface rules for CREATE TABLE and rename
use these laws. SchemaRuleExamples exercises both rules on abstract initial
connections. The affected tests are tests/test_model_package.py and
tests/surface_rebuild_test.py. The slice checks and review are pending.
