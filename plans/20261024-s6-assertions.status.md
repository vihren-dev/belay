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

## Readiness audit against production execution contracts

The 2026-10-24 audit of accepted `52cd08bf` found no new owner decision.
Refresh the task immediately before assignment to reuse the completed
`FreshTriple` bridges, `Sql.andOk`/`Sql.ifOk`, transformer laws and standard
specification rules. Fresh composition conveniences and assertion syntax remain
new work; do not duplicate the existing execution implementation.

Fresh entry uses `ExecutionContext.initial db env`, including the supplied
complete environment's counters. It does not force zero counters. The context
stores a raw connection. Default query assertions can use the existing raw
query observation and prove agreement with `Holds` under supplied validity;
`Branch.valid` provides reached validity for fresh runs. No new runtime validity
test or context field is needed. Context observations use the actual clock,
next-statement index and connection, and discard the observed step's resulting
connection. Equality bridges must account for pragma settings as well as clocks
and counters.

The task's reference to an existing explanation path is stale. The private
guide already promises `#explain`; S4 explicitly deferred it to S6 and the
editor task assigns it here. Providing that command is authorized work, with
later patterns and simulation extending it. This does not require another owner
choice. The before-context prerequisite remains unimplemented; full two-state
assertion acceptance still depends on it. Assign reusable effect/frame laws
once during the universal examples, then let the automation task consume them.

No assertion implementation or acceptance is claimed. Task-source edits remain
deferred until assignment, as requested by the owner.
