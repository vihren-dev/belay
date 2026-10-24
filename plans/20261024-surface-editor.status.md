# Status: SQL editor information and corrections

Created 2026-10-24. Status: OPEN. Implementation has not started.
Task: [task file](20261024-surface-editor.task.md).
Specs: ADR 0017 editor features and ADR 0016 layer boundaries.

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
