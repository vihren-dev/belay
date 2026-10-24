# Status: S6 effect rules and automation

Created 2026-10-24. Status: OPEN. Implementation has not started.
Task: [task file](20261024-s6-automation.task.md).
Specs: ADR17 S6; production execution/assertion/pattern tasks; S5 checker.

## Scope and inputs

This task completes the required proof tactics and their checked effect/frame
rules. It preserves the flexible semantic primitives. Dependency analysis is
conservative and supplies certificates to proved rules; disjoint table names
alone do not establish full commutation. The S6 prototype's counter, clock,
trigger and all-continuation examples remain acceptance cases.

The production execution, assertion and migration tasks plus S5 are
prerequisites. Final FK and table-rebuild work supplies the example semantics.
No production automation, general footprint engine or completion is claimed.

## Progress

- 2026-10-24: specified checked certificates, explicit proof routes, tactics,
  stable proof suggestions, S5 integration and private guide acceptance.
  Review 20261024T152950Z-8b118fbc found no musts or shoulds. Implementation
  remains unassigned pending its listed prerequisites.
