# Endpoint replacement experiment

Date: 2026-10-26. Audience: designers and reviewers.
Base: `6413afe3ff50`. Production code is unchanged.

## Established by the experiment

`ApiResolved.lean` derives six existing formulas with the existing generic run
rules. `ApiSurface.lean` derives five surface formulas. Each named proof uses
generic lifting and statement preservation evidence, not the old endpoint.
The final equality examples require the new and old declarations to have
definitionally equal types. Proof irrelevance proves equality after that type
check; it does not supply a stronger preservation result.

| Formula family | Named experiments |
| --- | --- |
| Raw conditions, no support premise | `sqlFromNotNull`, `sqlTypesFit`, `sqlFromChecksHold` |
| Support-sensitive admission | `sqlFromRowsWide`, `sqlAdmitted` |
| Fixed FK mapping and both atoms | `sqlFromForeignKeyAtoms` |
| Resolver-derived conditions | `scriptAdmitted`, `scriptNotNull`, `scriptTypesFit`, `scriptChecksHold` |
| Selected FK mapping with explicit conditions | `scriptRowReferences` |

All eleven declarations have `#print axioms` commands. Acceptance requires only
`propext`, `Classical.choice`, and `Quot.sound`. The design status records the
Nix result; direct compiler diagnostics are not acceptance evidence.

This is representative coverage. It does not prove that all 84 proposed
deletions integrate successfully. The implementation must compile the remaining
formulas, callers and tests after the old names are gone.

## Measured deletion inventory

`inventory.json` contains every declaration name and source span. A span starts
at the declaration's docstring and ends at its last nonblank line. It excludes
blank separators and includes any internal blank lines. The declaration/body
column excludes the preceding docstring. These are physical source lines.

| Family | Declarations | With docstrings | Declaration/body |
| --- | ---: | ---: | ---: |
| Run endpoints | 54 | 654 | 328 |
| Statement endpoints | 30 | 283 | 159 |
| Total | 84 | 937 | 487 |

The six modules that contain only removable specializations occupy 664 lines:
`AdmittedSqlRunsCatalog` (116), `AdmittedSqlRunsRows` (121),
`ScriptRunAdmittedCatalog` (66), `ScriptRunAdmittedRows` (74),
`RowLocalWriteTheorems` (171), and `RowLocalSchemaTheorems` (116).
Those full-file counts overlap the 937 declaration-span lines. They must not be
added to that total. No net-deletion or build-speed result has been measured.

The run inventory is the declarations whose names start with `runSqlFrom_`,
`runSql_` or `runScriptFrom_` in these modules, excluding the generic
`runScriptFrom_admittedWith`:

| Module | Count |
| --- | ---: |
| `ValidAtomsRuns` | 6 |
| `ValidAtomsTogether` | 2 |
| `KeysUniqueRuns` | 2 |
| `AdmittedSqlRunsCatalog` | 8 |
| `AdmittedSqlRunsRows` | 8 |
| `ScriptRunAdmittedCatalog` | 4 |
| `ScriptRunAdmittedRows` | 4 |
| `ScriptRunConstraints` | 5 |
| `ForeignKeyRuns` | 6 |
| `ForeignKeySchemaRuns` | 3 |
| `ForeignKeySelectedRuns` | 6 |

The statement inventory is all 15 theorems in `RowLocalWriteTheorems`, all 12
in `RowLocalSchemaTheorems`, and `runStatement_addColumn_notNull`,
`runStatement_addColumn_typesFit`, and `runStatement_addColumn_checksHold`.
The generic ADD COLUMN theorem and its atom-specific table facts stay.

## Consumers and deletion limits

Literal-name search across `packages`, `tests`, and `docs` found no references
to the 30 statement wrappers outside their own modules. The root barrel still
imports both removable statement modules.

Run endpoint callers in production source are `ScriptRunValid.lean` and the
model examples `AdmittedRunsConditionExamples`, `AdmittedRunsExamples`,
`KeysUniqueRunExamples`, and `ValidAtomsExamples`. The surface package calls
the separate `runScriptFrom_valid` and `runScriptStep_valid` helpers. Those
helpers are outside this inventory; removing a dependency of their proofs
does not remove their public guarantees.

Tests that require updates are `admitted_atoms_run_theorems_test.py`,
`keys_unique_theorems_test.py`, `valid_atoms_theorems_test.py`, and surface
fixtures `ForeignKeyRuns.lean`, `ForeignKeyDdlRuns.lean`, and
`ForeignKeyDdlDropRuns.lean`. The admitted test constructs names from a matrix,
so a literal-name search alone is incomplete. Module inventory tests and
barrel imports must also reflect deleted modules.

The three Python formula suites above are host-owned at the frozen base:
`tests/nix_suites.json` does not list them, `build-support/tests.nix` runs only
listed files, and `conftest.py` leaves unlisted files in `--source-checks`.
They run through `just test-source` against Nix-built libraries. The original
design registered their migrated formulas in the existing `model` Nix suite.
The owner's 2026-10-26 amendment to ADR 0025 D4 makes the exhaustive matrix
temporary: only lasting checks of current contracts remain in that suite. The
`compile_checks` helper is already an input of the suite.

`ValidAtomsRuns`, `KeysUniqueRuns`, `ValidAtomsTogether`, `ScriptRunConstraints`,
and the three FK run modules contain certificates, conditions, equivalences,
or general rules that are not in the deletion inventory. Removing their
specialized run endpoints does not justify deleting those other declarations.
In particular, retain `runScriptFrom_admittedWith` or its demonstrated generic
replacement and the explicit/selected FK correspondence.

## Contract amendments needed

The new ADR should replace the endpoint-identity obligation in ADR 0022 D3,
and identify its effect on these completed tasks:

- `20261023-keys-unique.task.md`, the run formulas at lines 54–67.
- `20261023-valid-atoms-theorems.task.md`, outcome 3 at lines 40–46,
  outcome 4 at lines 47–49, and the per-atom API statement at lines 136–137.
- `20261023-admitted-atoms-theorems.task.md`, outcomes 3–5 at lines 78–95.
- `20261024-foreign-key-atoms.task.md`, preservation over all three run forms
  at line 89 and the corresponding ADR 0022 D4 implementation record.

These records establish the semantic claims to retain. An amendment can
supersede the demand for named specializations without rewriting history or
removing the claims. ADR 0012 also names the old endpoints in its dated notes.

## Implementation acceptance requirements

The replacement API must derive each inventoried formula with its current
hypotheses or weaker ones. An invariant that does not need readiness must
remain usable without it. An implementation must not replace independent
atoms with a requirement for `Database.Valid`.

Raw resolved runs must retain their explicit statement conditions. Surface
admission and constraint claims must continue to derive those conditions from
resolution, execution mode and matching limits. Conditional FK claims must
retain their explicit mapping and their schema/row distinction.

All retained outcome stores and transaction snapshots remain covered. Partial
FAIL and stopped-suffix examples keep their current conclusions. Existing
necessity counterexamples remain; tests must not become less discriminating
because the named wrapper no longer exists.

Formula checks must instantiate the generic rules directly, audit the actual
proofs' axiom closure, and compile against the post-deletion package. There
must be no forwarding aliases or replacement endpoint matrix. All inventoried
old names disappear from active implementation and tests; historical records
may mention the names with an explicit supersession note.

The implementation records net line and module counts separately from this
inventory, including any new generic proofs or documentation. Claims about
compilation time require a controlled measurement; wrapper deletion alone is
not such a measurement.
