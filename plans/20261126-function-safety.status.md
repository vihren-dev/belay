# Function safety status

Created 2026-11-26. Status DONE. Task: [Function safety in expression proofs](20261126-function-safety.task.md).

ADR 0015 defines scalar and JSON functions. The function dispatchers are in
`Queries/Evaluation/Scalar.lean` and `Values/Json/JsonApply.lean`. The expression library now exports
`scalarSucceeds` and `jsonSucceeds`. The proofs cover every constructor. Text and binary
extraction share `ExtractInputs`. The DELETE tactic uses the catalog laws and its existing
extension attribute. The zeroblob fixture needs only a size bound. The expression model also exports the
implication from successful extraction to safe paths for use by proof search. The model root
imports the function laws and the statement coverage laws. The surface tactic imports this
public root to follow the package boundary.

Local development checks passed for the build, the eight model proof fixtures, the three
failure boundaries, the fourteen DELETE proofs, the DELETE/SELECT comparison, and the five
ownership checks. Release evidence comes from the Nix checks.

Nix verification passed on the final source. The full test reports are
`gxlki1kjdr2rq0qzl5iw54syymnmbqjy-belay-test-reports`, including the 34 surfaceSelect
tests. The public documentation inventory and the frozen-corpus verdict
(`yp87jlilchv1ahpc0mbaqgjivyngi5pa-belay-verdict`) passed. The separate source suite passed
all 581 selected tests. The model suite passed on retry after one concurrent run exceeded
the generated conformance test's time limit.
