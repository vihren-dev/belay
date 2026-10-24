# Status: SQL editor information and corrections

Created 2026-10-24. Status: OPEN. Implementation is assigned.
Task: [task file](20261024-surface-editor.task.md).
Specs: ADR 0017 editor features and ADR 0016 layer boundaries.

## Owner request

On 2026-10-24 the owner instructed: "continue working until adr17 is done.
after specifying a task in a task file the task should be done by a subagent."
The request also requires separate workspaces for parallel tasks, disjoint
edits and sufficient resources. The scope interpretation and review disposition
below explain why this task closes ADR17 work rather than adding a new goal.

## Evidence and constraints

The read-only editor/doc-block audit found no SQL hover/provenance registry,
name-fix emitter, trap linter or actual LSP fixture in the inspected surface.
Existing translator spans, parameter plans, resolver scope/affinity and native
Lean info/code-action APIs are the reusable inputs. No server feasibility
probe has run; compiler-source inspection alone is not acceptance evidence.

The owner kept the current DQS-on/FK-off defaults. The separate private guide
correction implements that decision. Doc-block syntax and S7 formatting have
their own pending decisions; this task changes neither contract.

## Progress

- 2026-10-24: specified observable server behavior, exact source and scope
  requirements, missing-origin behavior, bounded typo corrections, and warning
  evidence. Task review and an isolated implementation workspace are next.
  Schema integration must coordinate with the active query-source owner.
- 2026-10-24: independent review `20261024T132607Z-11cc3da1` found no musts
  and one scope-attribution should. The task now connects its required behavior
  to the owner's ADR17 completion request and the existing S2/S3 SQL forms.
- 2026-10-24: follow-up review `20261024T132710Z-9383cec2` found no musts and
  repeated the scope should. Rejected with a recorded reason: ADR17 keeps the
  guide as its target and assigns these editor behaviors to slice task design;
  it does not defer them beyond completion. These are public SQL surface
  behaviors for existing forms, not speculative support infrastructure. The
  owner's completion request therefore remains the authority for this scope.
- 2026-10-24: final task review `20261024T132927Z-4be46bc9` has no findings.
  The task still matches that reviewed revision byte for byte. Assigned its
  first acceptance part to `text_build_boundaries` in isolated
  `sqlite-verifier-surface-editor`, based on checked search/execution integration
  `3a632d10`. The same worker owns the frozen S7 parameter/source helpers and
  the checked doc-block unit, so shared interfaces can be coordinated without
  concurrent edits. Existing SQL terms, parameter semantics and source metadata
  must remain unchanged. The actual Lean server, including hover ranges and
  semantic-token responses, supplies required first-part evidence.
  Schema/origin/correction/warning behavior remains in the second part and needs
  the completed query-source interfaces. The first coherent checked commit
  will await independent review after the reviewer login refresh. No editor
  implementation or acceptance result is claimed here.
