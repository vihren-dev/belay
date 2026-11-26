# Function safety status

Created 2026-11-26. Status DONE. Task: [Function safety in expression proofs](20261126-function-safety.task.md).

ADR 0015 defines scalar and JSON functions. The function dispatchers are in
`Queries/Evaluation/Scalar.lean` and `Values/Json/JsonApply.lean`. The expression library now exports
`scalarSucceeds` and `jsonSucceeds`. The proofs cover every constructor. Text and binary
extraction share `ExtractInputs`. The DELETE tactic uses the catalog laws and its existing
extension attribute. The zeroblob fixture needs only a size bound.

`just dev-build` passed. The function-law fixtures check eight independent model proofs,
three failure boundaries, 14 DELETE proofs and the DELETE/SELECT comparison through
`tests/surface_select_sources_test.py::test_context_cases`. The five tests in
`tests/test_test_ownership.py` and `tests/test_model_ownership.py` passed.
