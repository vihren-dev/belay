# Status: S6 migration views and patterns

Created 2026-10-24. Status: OPEN. Implementation has not started.
Task: [task file](20261024-s6-migration-patterns.task.md).
Specs: ADR17 S6 and the accepted explicit observation-view decision.

## Scope and dependencies

The owner accepted a migration observation view instead of a quiet action that
changes ordinary execution or equivalence. Query preservation/translation use
an explicit weaker comparison; commutation compares the projected trace and
complete non-trace context. Failures, return values, counters and clock effects
remain real. The positive expansion application theorem belongs to S8 scoped
simulation because its write order changes total_changes.

The production execution task is the main prerequisite. Final table-rebuild and
FK work is needed for the cascade example. Existing reviewed native diagnostics
inform these contracts but are not implementation acceptance. No production
view/pattern modules are claimed in this planning tree.

## Progress

- 2026-10-24: specified view erasure/projection, exact pattern domains, contextual
  comparison laws and universal example acceptance. Review
  20261024T152701Z-56b9f410 found no musts or shoulds. Implementation remains
  unassigned pending the listed prerequisites.
- 2026-10-24: readiness audit against complete execution source `5bc323f0`
  found the first acceptance part can start independently of the later FK,
  rebuild and assertion-notation work. Reuse `Sql.runFrom`, `Sql.Branch`, its
  actual-run and bind laws, `ExecutionContext.finish`, `SucceedsFrom`,
  `EquivAt` and `ObservationEquivAt`. The compared trace can be projected;
  execution continuations must still receive their selected raw or concrete
  output. The reached index uses the original trace length, not the projected
  length. Preserve values, errors and stopped outcomes.
  Use `SucceedsFrom` for migration success at the original context; `andOk`
  also constrains the prior trace and would narrow that domain. Query admission
  uses `Script.isQuery` and `Syntax.Statement.readsOnly`; the program `query`
  helper checks statement count and is not a read-only premise. New view and
  pattern modules can own separate fixtures and narrow manifest additions.
  No implementation is assigned yet, and the whole task remains open.
