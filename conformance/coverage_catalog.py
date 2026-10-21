"""The documented claims that the conformance evidence traces, as an inventory and not as measured coverage."""

CLAIMS: tuple[dict[str, str], ...] = (
    {"reference": "R-42316-09582", "snapshot": "conformance/upstream/e_createtable.test:854",
     "claim": "Omitted defaults yield NULL", "model": "packages/belay-sqlite-model/Belay/Sqlite/Model/Database.lean: Table.appendColumns",
     "evidence": "alter3-3.2; derived ADD then CREATE"},
    {"reference": "R-25473-20557", "snapshot": "conformance/upstream/e_createtable.test:1059",
     "claim": "Column count is bounded",
     "model": "packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/Definitions.lean: resolveAddColumn",
     "evidence": "derived column-limit cases at 2,000 columns and under a limit lowered to 5; native MAX_COLUMN pin"},
    {"reference": "R-27775-64721", "snapshot": "conformance/upstream/e_createtable.test:1074",
     "claim": "Runtime limits can be lowered",
     "model": "packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/Profile.lean: Profile.limits",
     "evidence": "native model cases recorded under a column limit lowered to 5; Lean resolution examples under a lowered limit"},
    {"reference": "lang_altertable.html#alter_table_add_column",
     "snapshot": "conformance/upstream/lang_altertable.html",
     "claim": "ADD appends a column", "model": "packages/belay-sqlite-model/Belay/Sqlite/Model/Database.lean: Table.appendColumns",
     "evidence": "derived ADD cases and model preservation; physical no-rewrite claim unmeasured"},
    {"reference": "limits.html#max_column", "snapshot": "conformance/upstream/limits.html",
     "claim": "Default maximum column count is 2000",
     "model": "packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/Profile.lean: Limits.documentedDefaults",
     "evidence": "native MAX_COLUMN pin and derived boundary case"},
)

EXCLUSIONS: tuple[str, ...] = (
    "No proof of native SQLite C refinement or parser equivalence",
    "No instrumented grammar-production execution coverage",
    "No denominator for all documented SQLite behavior or the full upstream corpus",
    "Runtime corpus and scoped execution coverage are separate source-bound reports; no whole-SQLite denominator",
    "No native storage-layout, schema-cookie, coercion, or arbitrary-query proof",
)
