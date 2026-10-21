import Belay.Sqlite.Model
import SqliteVerifier.Contract
import SqliteVerifier.Library
import SqliteVerifier.SchemaProjection
import SqliteVerifier.NullableProjection
import SqliteVerifier.ApplicationKeys
import SqliteVerifier.ApplicationKeyPreservation

set_option doc.verso true

/-!
Import this module to use the stored-data model, logical contracts and reusable
schema proofs. A certificate establishes the written model obligations;
native SQLite conformance is assessed separately.

Start with {name}`Belay.Sqlite.Model.Catalog`: the tables and indexes that resolution
computes from the schema, with names as written and columns that keep their
declared type text. The database maps catalog positions to tables. A valid
catalog has a finite empty-data witness, useful when proving nonempty admission:

```lean
open Belay.Sqlite.Model SqliteVerifier
example : Conforms (Profile.documented "3.51.0" "build") [] (Catalog.emptyDatabase []) :=
  Catalog.emptyDatabase_conforms (by decide)
```

Choose the observation and change relation explicitly. Use
{name}`SqliteVerifier.projectedInterpretation` and
{name}`SqliteVerifier.LogicalContract.preservation` when physical rowids and
stored row order matter.

For a different policy, construct {name}`SqliteVerifier.Interpretation` and
{name}`SqliteVerifier.LogicalContract` directly. Their invariant, observation,
validity, change, schema, failure and applicability fields remain the general
interface. Supply {name}`SqliteVerifier.requiresSuccess` when open transactions
and failures must be excluded by the proof.

The target is {name}`SqliteVerifier.VerificationConditions`: a starting witness,
sound before/after/failure representations, the starting invariant, support for
every admitted database, and applicability plus result obligations for every
related outcome. Its script is the resolved migration, and its catalogs are the
starting and resulting catalogs that resolution computes. {name}`SqliteVerifier.VerificationConditions.of_runSql` lets
users prove those outcome obligations from the computed SQL result while
retaining the universal support premise. {name}`Belay.Sqlite.Model.SchemaOnly`
guards the current schema-extension preservation laws.

Engineering examples and demonstrations are test code in the separate
`EngineeringExamples` library. This module does not import them.

For command-line verification, supply approved schema, requirements and current
interpretation files, plus candidate SQL, next interpretation and proof files.
Preparation binds those exact inputs to the generated target; the checker then
checks the exported certificate. CLI help describes command options and result
codes. A library theorem alone does not bind an arbitrary candidate file.
-/
