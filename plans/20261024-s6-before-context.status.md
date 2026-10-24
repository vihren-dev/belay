# Status: S6 initial/current query context

Created 2026-10-24. Status: OPEN. Implementation has not started.
Task: [task file](20261024-s6-before-context.task.md).
Specs: ADR17 S6 and the checked foundations prototype.

## Evidence and prerequisites

The prototype confirms that before-qualified queries are rejected and that the
current evaluator has one database origin. The guide explicitly requires fixed
initial-database observations. A bounded read-only context supplies that behavior
through the existing model; a general connection attachment feature is unnecessary.

Implementation waits for the completed query-source/CTE/view representation and
reserved ownership of its resolver/evaluator files. The pending S6 equivalence
and universal guide-effect decisions do not change this primitive's meaning.

## Progress

- 2026-10-24: specified exact origins, metadata/context propagation, conservative
  extension laws and native two-database observation tests. Await task review.
  No production change or task acceptance result is claimed.
