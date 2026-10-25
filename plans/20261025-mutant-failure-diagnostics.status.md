# Mutation failure diagnostics status

Created 2026-10-25. Status: OPEN.
Task: [required outcomes](20261025-mutant-failure-diagnostics.task.md).

The published #250 hosted log reports three failed groups before outer timeout
exit 124, without final pytest failure details or a general-mutant report
artifact. The task preserves complete successful-run coverage and all existing
limits while making an already reported failure diagnosable. It does not infer
the cause of the query/JSON failures.

Task review `20261025T013944Z-ef3c7307` found no must findings and one R19 should:
state why scheduled acceptance excludes broad local mutation runs. The task now
cites the owner's restriction and requires an actual hosted manual run, since
the PR change filter skips mutation jobs for this change. The finding is fixed;
clarification review `20261025T014013Z-d7844328` has no findings. The
implementation base is published #251, `fe169099`; the view worker takes
this bounded follow-up in an isolated workspace after task review.

The isolated `mutant-failure-diagnostics` workspace is ready on `fe169099`.
Its four development-shell configuration files match the approved planning
workspace byte for byte; `direnv allow` used the owner's standing authorization.

## Implementation and command inspection

The common Nix suite command appends pytest's `--exitfirst` only for names in
the existing `tests/nix_mutant_suites.json`. A reported failure therefore ends
that suite before later groups consume its budget. The successful path keeps
the same complete test-file inventory and assertions. No runner or plugin is
added; the independent CI matrix's `fail-fast: false` is unchanged.

The existing evaluated-command test checks the conditional flag along with the
complete file list, 300-second per-test limit, 2700-second mutant suite limit,
1200-second ordinary suite limit and report arguments. The focused command,
routing, ownership, scope and limit checks are local diagnostics only;
the Nix acceptance gates follow independent review.

Before/after evaluation of all 14 suite commands is retained under
`build/agent-logs/mutant-diagnostics-{before,after}.json`. The three mutant
commands differ only by `--exitfirst`; all eleven ordinary commands are
byte-identical. Only the three mutant derivations and the surface derivation
change: the surface layer checks read the changed build configuration, although
its command is unchanged. Earlier mutant results are not claimed as acceptance
of the changed command. No broad local mutant suite runs.

`mutant-diagnostics-command-comparison.json` records these equalities and the
unchanged protected trees. Packages, conformance/native/corpus sources, judge,
integrity and oracle inputs match `fe169099`. The judge lock SHA-256 is
`3ed3054ac313591582e038ecad92b04c81fea33d2559a97ba5a847198196831c`.
Post-review full/verdict and task-end Nix/scheduled checks are assigned heavy
slot 1. The task remains OPEN until the required hosted manual run is inspected
after publication; a skipped PR mutant job is not execution evidence.
