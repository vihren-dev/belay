# Status of success of a literal INSERT

Created 2026-11-19. DONE on 2026-11-20. [Task](20261119-literal-insert-success.task.md).

The statement and step parts of the issue can proceed independently of
the validity bridge. The proposed old-table freshness premise admits two
new equal rowid aliases on an empty table. The owner resolved this on 2026-11-20.

PlainInsertSuccess gives the single ready statement effect, updated rows and
change count. PlainInsertStep gives the continued script step, done output
and updated counters. PlainInsertStepCases applies the step law to two
literal rows and checks a conflicting batch on an empty table. The fixture
runs through tests/surface_schema_script_test.py.

Review clarified the exact ready run and its alternatives. SchemaScriptReplays
now compares the successful literal batch and the duplicate batch with pinned SQLite.

The second review of the statement and script laws found no issues. The
validity bridge was deferred until the owner chose a premise for keys within a batch.

The [full Nix suite](https://github.com/vihren-dev/belay/actions/runs/44579073231/job/135754436979) and the [verdict](https://github.com/vihren-dev/belay/actions/runs/44579073093/job/135754435913) passed for the statement and step laws.

On 2026-11-20 the owner approved pairwise uniqueness of new keys in
addition to their freshness against stored keys. The regression is
`tests/surface_schema_script_test.py`.

LiteralInsertFits derives the stored rows' constraints and the alias affinity
from database validity. Its general law checks the allocated rowids, generated
cells and SQL keys of the incoming batch. Its explicit-alias law uses rowid
freshness for every key that contains the alias. PlainInsertStepCases uses
the laws for two explicit ids and an allocated id on a populated table with
a secondary UNIQUE key. SchemaScriptReplays also exercises a NOCASE collision
within a batch.

The package boundary test found the new module missing from the core
library manifest. The manifest now includes LiteralInsertFits. The
regression is `tests/test_model_package.py::test_root_imports_the_core_and_only_the_prelude`.

The full Nix suite passed, including the public Lean proofs and pinned SQLite
replay. The report is `56qg0ixg91qm1qz4ryji895mdhy2hcbm-belay-test-reports`. The verdict
passed for all 59 frozen corpora. On the combined stack, `just test-nix`
passed all 99 selected host tests and `just test-scheduled-checks` passed.
