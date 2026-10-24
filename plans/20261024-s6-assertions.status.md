# Status: S6 fresh-run triples and assertions

Created 2026-10-24. Status: OPEN. Implementation has not started.
Task: [task file](20261024-s6-assertions.task.md).
Specs: ADR17 S6; accepted fresh-run and explicit effect-premise decisions.

## Scope and inputs

The owner accepted an explicit fresh-run helper on 2026-10-24. Ordinary Std.Do
triples retain arbitrary contexts. The helper fixes the initial database,
complete environment, initial connection, index zero and empty trace. Existing
Holds retains its default observation; context-aware assertions have a separate
name. Before always refers to the captured start, including after bind.

Execution contracts and the initial/current query task are prerequisites. The
checked S6 prototype established the candidate transformer and soundness route,
but supplied neither production assertions nor before-query semantics. The
universal guide examples need the accepted schema and trigger/FK conditions;
native trigger counterexamples remain required negative fixtures.

## Progress

- 2026-10-24: specified fresh/ordinary equivalence, observation distinctions,
  compositional rules and universal guide acceptance. Review
  20261024T152453Z-8687f111 found no musts and one naming should: the predecessor
  specifies conditional/total policies but does not prescribe helper names.
  This task now explicitly supplies ifOk/andOk over those policies. No
  implementation or Nix acceptance is claimed.
- Follow-up review 20261024T152713Z-33693f10 has no musts or shoulds.
