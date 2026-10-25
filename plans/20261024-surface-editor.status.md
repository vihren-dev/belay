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
their own accepted tasks; S7 package-root ambiguity remains a separate owner
decision. This task changes none of those contracts.

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
- 2026-10-25: carried the exact reviewed task/status and all three review records
  in `7bd4adde`, on immutable `3a632d10987e232ccbf818ce49b1936b2758c969`.
  The four shell files match the approved doc-block workspace; standing dev-shell
  authorization applies. The other task workspaces remain frozen.
- 2026-10-25: implemented the first source/parameter unit in the isolated editor
  workspace. `SqlEditorSource` supplies an explicit byte-range map and checks
  source-byte agreement before creating original-source information.
  `SqlParameterInfo` consumes existing plan slots and translator numbers; it adds
  native term/hover information without another numbering rule. `SqlTerm` retains
  each captured expression before coercion, uses its coerced value in the original
  script construction, and leaves source/replay annotations intact. The changed
  `variableValue` pair return needs a mechanical adaptation when the frozen S7
  shared builder is later integrated; no old workspace was edited.

## First-unit evidence and remaining acceptance

The production source is frozen at `a075cb27a400e89cb2fafa6298e9d56ef113a450`.
The test runtime correction is in snapshot
`44b4286cd2fd710a26ce0e174102823523f0fc8c`, with identical production files.

- Focused Nix real-server checks passed: 2 passed, 89 deselected, report
  `/nix/store/8d538sd8bf49gx9qqnrd8rimpcaxbs27-sqlite-verifier-test-surface-1`.
  They run the actual pinned `lean --server`, supplying installed artifacts via
  the existing module-setup contract. LF and CRLF fixtures check exact UTF-16
  hover ranges after non-BMP text, 19 parameter occurrences, pre-coercion
  `String`/`Int64`/`Value` types, do locals and constants, generated names/numbers,
  repeated parameters and per-statement slot changes, aliases and sparse slots.
  Native definition requests identify captured binders/constants/do locals.
  Local and generated arguments receive native variable semantic tokens;
  constants retain native constant behavior. SQL keywords and uncertain escaped
  mappings receive no extra tokens.
- The earlier selected Nix run had 17 passing compatibility/layer checks and
  two failed server starts. Pinned Lean's watchdog reads the UTC zone file;
  the suite lacked timezone data in the sandbox. The corrected surface test
  derivation sets `TZDIR` to pinned `pkgs.tzdata`, without a host dependency.
  The two-case retry above is successful acceptance evidence for the server.
- The development build and local diagnostics are not acceptance evidence.
  Local compatibility exposed an independent baseline S5 regression:
  `CheckReplayData` globally registers `ToExpr Output`, so `#eval` selects Lean
  constructor printing instead of the existing custom `Repr`. A diagnostic
  control removes only that instance attribute and restores `[done 1]`.
  Root confirmed the baseline cause and assigned its repair to the S5 owner.
  Existing `GuideParameters` expectations are unchanged. Logs and the control
  are under `build/agent-logs/`.

The first coherent source commit awaits integration of that S5 repair and a
combined focused Nix check of the editor, guide parameters and replay/search
compatibility. Root has authorized a new merge of the frozen snapshots, without
rebasing shared ancestors. No process is live; the heavy slot is released.
Root's source read found no semantic issue, but it is not independent review.
Claude review remains blocked by the reported expired login; no retry was made.
First-part full/verdict acceptance follows its independent review. Schema facts,
table origins, corrections and warnings remain in the second part, together
with completed query-source integration. The overall task remains OPEN.
