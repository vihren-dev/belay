# Function safety status

Created 2026-11-26. Status DONE. Task: [Function safety in expression proofs](20261126-function-safety.task.md).

ADR 0015 defines scalar and JSON functions. The function dispatchers are in
`Queries/Evaluation/Scalar.lean` and `Values/Json/JsonApply.lean`. The expression library now exports
`scalarSucceeds` and `jsonSucceeds`. The proofs cover every constructor. Text and binary
extraction share `ExtractInputs`. The DELETE tactic uses the catalog laws and its existing
extension attribute. The zeroblob fixture needs only a size bound. The expression model also exports the
implication from successful extraction to safe paths for use by proof search. The model root
imports the function laws and the statement coverage laws.

Local development checks passed for the build, the eight model proof fixtures, the three
failure boundaries, the fourteen DELETE proofs, the DELETE/SELECT comparison, and the five
ownership checks. Release evidence comes from the Nix checks.
