# Status of named SQL claims

Created 2026-11-17. DONE. [Task](20261117-named-check-claims.task.md).

Tooling/Counterexamples/CheckAutoProof.lean selects the proof route after
Programs/Automation/CheckAutoProof.lean opens the claim. The opening now expands user definitions inside the search budget and records
the names in the replay script. SelectCheckCases.lean covers a named claim,
its alias and a named false claim. The tests are test_background_checking
in tests/surface_select_procedure_test.py and tests/surface_search_test.py.

The guide shows how to check a claim by name. The library module roots
that the checker preserves are documented beside the opening tactic.

The hosted S6 proof replay exposed an opening instruction that required
the original user-defined name even when the replay restated its expanded
body. The generated proof unfolds the names when present and also accepts
the expanded body. The named and expanded replay checks are in surface_select_procedure_test.py and
surface_s6_check_programs_test.py.

The [Linux Nix checks for the named-claim PR](https://github.com/vihren-dev/belay/actions/runs/44207582153/job/134477404700)
passed on 2026-11-18. The printed named and expanded proofs elaborated in
the S6 fixture. The frozen verdict matches main on all 7,868 cases.
The final stack passed all 1,483 tests in the 22 Nix reports, the 98 Nix
infrastructure tests, and the scheduled checks.
