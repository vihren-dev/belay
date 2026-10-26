# Row-engine proof boundary experiment

Date: 2026-10-26. Audience: designers and reviewers.

## Decision: defer the row-engine abstraction

Both prototypes prove shared reasoning with the existing mathematical assumptions.
Neither demonstrates a useful reduction in the code that must be maintained.
Keep the production trigger proofs. Retain these experiments as evidence for the
decision; do not schedule a row-engine migration from this result.

The repeated control flow is real. However, the general contract needs explicit
work permissions, bookkeeping closure and separate success/stop predicates.
Those obligations are inexpensive inside the two existing specialized proofs.
Moving them into a shared interface introduces larger definitions and witnesses.
The narrower program/list boundary avoids the work interface, but its witnesses
still exceed the four existing program/list proofs in the measured source.

## Original contracts and boundaries

All production paths below are relative to
`packages/belay-sqlite-model/Belay/Sqlite/Model/` at the experiment base revision.

`RowEngineTriggers.lean:16` defines `NestedRun.Keeps`: for every frame, work and
input state, the database invariant on that input implies the corresponding
success or stop invariant. Its state predicate is `KeyState.Holds invariant
catalog`; its stop predicate is `KeyStop.Holds invariant catalog`.

`ForeignKeyWorkConditions.lean:57` defines `NestedRun.ForeignKeyKeeps`: the
corresponding FK claim additionally assumes matching frame programs and
`RowWork.ForeignKeySafe catalog`. Its predicates, defined in
`ForeignKeyEngineFacts.lean:18` and `:23`, are:

```lean
KeyState.ForeignKeyInvariant profile catalog state :=
  state.Holds (Database.ForeignKeyReady profile) catalog ∧ state.CounterBound catalog
KeyStop.ForeignKeyInvariant profile catalog stop :=
  stop.Holds (Database.ForeignKeyReady profile) catalog ∧ stop.CounterBound catalog
```

`Database.ForeignKeyReady` means admission and unique keys. It permits outstanding
row-reference violations; the immediate counter bounds them. The stop contract
requires the full invariant for FAIL, admission and unique keys for rollback,
and nothing for raw errors or undescribed stops. A uniform lifting of the success
predicate to every stop carrier would change this contract.

The FK conditions also cover actual generated UPDATE work. They do not follow
from a predicate on `KeyState` alone. Likewise, the generic state predicate must
remain true after `afterStep` and query bookkeeping. The specialized predicates
ignore those bookkeeping fields, so their closure proofs reduce immediately.

The physical phases remain separate. In `ForeignKeyCounterDelete.lean:49–70`,
the proof establishes the counter bound after both `oldSteps` and physical row
removal. It does not require the same invariant after each operation in that
phase. `NestedRun.BeforeUpdateFrame` (`ForeignKeyWorkConditions.lean:66`) also
retains its independent target-row condition.

## Broad prototype

`RowContract.lean`, `RowControl.lean` and `RowInstances.lean` introduce:

- `RowKeeps P Q allowed nested`, with separate predicates on `KeyState` and
  `KeyStop`, plus permission on the actual frame, work and input state.
- `RowControlFacts P Q`, for bookkeeping closure and the actual stop constructors.
- `StepAllowed`, for the work that each INSERT, UPDATE or DELETE step generates.
- Shared proofs for RAISE, trigger entry, step dispatch, program execution and
  the fired-program list.
- `databasePrograms` and `foreignKeyPrograms`, which derive the two existing
  program-list formulas with their original assumptions.

The proof does not call the old specialized trigger traversal theorems. Its FK
permission is `frame.programs = programs ∧ work.ForeignKeySafe catalog`.
The actual inner running frame and the INSERT conflict algorithm are retained.

The main cost is `StepAllowed`: it repeats the work-construction expressions in
`TriggerRun.runStep` (`TriggerRun.lean:105`). The contract and its FK witness
therefore add another place to update when those expressions change. This is
the opposite of the intended maintenance benefit.

## Narrow prototype

`RowNarrow.lean` proves `programFromEffects` and `programsFromEffects` by unfolding
and traversing the real program body and fired list once. They take the local
entry/step or program result contracts as premises, preserving independent
`P : KeyState → Prop` and `Q : KeyStop → Prop`.

`RowNarrowInstances.lean` derives all four original program/program-list formulas.
It calls the existing local `enterProgram_*` and `runStep_*` facts. It does not
call `runProgram_holds`, `runPrograms_holds`, `runProgram_counterBound` or
`runPrograms_counterBound`. Thus the shared traversal is actually proved, while
step dispatch and its domain conditions deliberately remain specialized.

## Measured source inventory

Physical lines include blank lines and comments. Code lines count nonempty lines
after removal of Lean block comments. The same convention is used for each row.
Experimental totals include their imports, namespaces and axiom-print commands;
production totals include those present in the stated files or declaration spans.
These are source inventories, not a measured production migration delta.

| Source | Physical lines | Code lines |
| --- | ---: | ---: |
| Original `RowEngineTriggers.lean`, whole file | 111 | 64 |
| Original `ForeignKeyCounterTriggers.lean`, whole file | 98 | 75 |
| Original full pair | 209 | 139 |
| `RowContract.lean` | 76 | 50 |
| `RowControl.lean` | 96 | 79 |
| `RowInstances.lean` | 104 | 73 |
| Broad prototype total | 276 | 202 |
| Original ordinary program/list declarations and docs, lines 70–109 | 40 | 28 |
| Original FK program/list declarations and docs, lines 55–96 | 42 | 34 |
| Original four narrow endpoints | 82 | 62 |
| `RowNarrow.lean` | 57 | 44 |
| `RowNarrowInstances.lean` | 67 | 48 |
| Narrow prototype total | 124 | 92 |

The original full pair contains ten handwritten theorems in five matching roles.
The narrow experiment replaces four proof bodies with two shared proofs and four
formula witnesses. Counting only the generic proofs would omit the work needed
to recover the claims that callers use.

## Caller audit

Each single-program endpoint has one implementation consumer: its corresponding
program-list theorem (`RowEngineTriggers.lean:109` and
`ForeignKeyCounterTriggers.lean:93`). The program-list endpoints have these
production call sites:

| Endpoint | Code call sites | Consuming theorem bodies |
| --- | --- | ---: |
| `runPrograms_holds` | `RowEngineDelete.lean:49,63`; `RowEngineInsert.lean:97,123`; `RowEngineUpdate.lean:114,117,123` | 3 |
| `runPrograms_counterBound` | `ForeignKeyCounterRows.lean:22,56,75` | 3 |

There are ten textual code calls in six theorem bodies, excluding doc references.
Most calls apply an endpoint directly to the nested-run contract and current
invariant. Removing these endpoints would require generic entry, step and list
witnesses at those sites, including the FK membership/safety discharge. Keeping
specialized adapters would retain simple calls, but also retain those adapter
obligations beside the new generic interface. No migrated consumer implementation
has demonstrated a net simplification. The audit therefore supports deferral,
not adoption conditional on hypothetical wrapper deletion or future consumers.

## Validation and scope

Development compilation succeeded without warnings using the pinned Lean 4.34.1
compiler and compiled model libraries. Compile order is `RowContract`,
`RowControl`, `RowInstances`, `RowNarrow`, `RowNarrowInstances`. Each file is under
200 lines and enables checked Verso docstrings. The standalone Nix experiment
check supplies acceptance evidence; local compilation alone does not.

The files print proof closures for `rowStep`, `rowProgram`, `rowPrograms`,
`databasePrograms`, `foreignKeyPrograms`, `programFromEffects`,
`programsFromEffects`, and all four narrow formula witnesses. Each inspected
closure reports only `propext`, `Classical.choice` and `Quot.sound`. The endpoint
closures include the intermediate shared lemmas they use.

No fuel induction or complete physical DELETE, UPDATE or INSERT preservation
proof was generalized. The experiment changes no engine execution or production
proof. It establishes neither a compile-time improvement nor a smaller rebuild
scope. Any later proposal must demonstrate a concrete reduction across the shared
interface, its witnesses and actual migrated consumers while retaining the stop,
work and phase distinctions above.
