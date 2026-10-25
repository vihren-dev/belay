# S7: proof-cost reporting, production

Created 2026-10-25. Status: OPEN. The six decisions at the end were answered
on 2026-10-25; the outcomes below follow them.
Status: [progress](20261025-s7-proof-costs.status.md).
Specs: [ADR 0017](../docs/adr-0017-user-surface.md), D1, the S7 row and the
"S7 cost clarification" paragraph; the completed
[collector prototype](20261024-s7-proof-cost-prototype.task.md) and its
[measurement findings](../docs/s7-proof-cost-findings.md); the S7 files
[task](20261024-surface-s7-files.task.md) (the shared checker). The private
guide promises, in "Stable proofs", `lake exe belay-sql-check --costs` and a CI
failure when a proof's cost grows by more than a bound that the user sets.

## Purpose

The owner asked for per-proof heartbeat reports and a user-set CI growth bound
(ADR 0017, S7). The prototype showed what Lean can measure and the owner
accepted the contract: report completed, explicit, named proof-body
elaboration. This task ships that contract as an optional collector in the
`Belay` library and a `--costs` mode of the existing checker. It adds no
baseline manager, history, dashboard, default allowance or profiler. Each of
those is outside the owner's request.

## What is true at the base (checked at `e384c875`)

- No production collector exists. The only collector is the prototype's
  test-only code in `tests/surface/ProofCost{Records,Collector,Cases,Surface}.lean`,
  driven by `tests/proof_cost_test.py` and `tests/proof_cost_support.py`.
- The prototype registers one `command_elab` for `Lean.Parser.Command.declaration`
  and none for `Lean.Parser.Command.mutual`. Local probe, 2026-10-25, Lean 4.34.1,
  prototype code, diagnostic only: a `mutual` block of two theorems gives no
  record. A second handler for `mutual` that delegates to
  `Lean.Elab.Command.elabMutual` gives one record for each theorem. Native mutual
  coverage is therefore feasible; the mutual test below turns the probe into
  evidence.
- The same probe shows that the prototype leaves the native trace line
  (`[Elab.definition.value] [2853.000000] ... a`) in the compiler output.
- Neither prototype handler carries `@[incremental]`. Lean's command loop
  (`elabCommandUsing` in `Lean/Elab/Command.lean`) removes the snapshot context of
  a handler without that tag, and the built-in `elabDeclaration` and
  `elabMutual` have it (`builtin_incremental`).
- The prototype option `proofCost.enabled` defaults to true. When it is false, the
  handler still reads the command state and stores an empty pending entry. There
  is no bypass.
- The S5 automatic check is a native command linter (`automaticLinter` in
  `Belay/Sqlite/SqlAutomatic.lean`, registered with `Command.addLinter`). It runs
  after the declaration handler on the completed command, finds statements with
  `Check.statements` (`CheckDeclarations.lean`), and does not replace a handler.
- `lake exe belay-sql-check` (`packages/belay/BelaySqlCheck.lean`, 171 lines)
  takes only `[--library NAME]`. Its exit codes are 0 (all SQL sources fresh),
  1 (stale) and 2 (a library could not be read). It reads each compiled module
  with `readModuleData` and decodes stored entries of
  `Belay.Sqlite.SqlSourceRecord` with an unchecked cast. It builds nothing.
  Rule 6 of `tests/surface_layers_test.py` lets only the `BelaySqlCheck` module
  import Lake. `just dev-build` does not build this executable.
- The `Belay` library lists its modules in `packages/belay/lakefile.lean` and has
  `precompileModules := true`. The barrel `Belay/Sqlite.lean` does not import
  `SqlSourceRecord` or `SqlCheckReport` itself.

## Required outcomes

Cost data is exact internal heartbeat units (1000 internal units are one Lean
budget unit). No outcome may turn missing data into zero.

1. **Collection is optional, and "off" is a bypass.** (Coordinator decision, 2026-10-25.) A user turns collection
   on with a `Bool` option (default false) that works in a lakefile through the
   `weak.` prefix and with `set_option ... in`. With the option off, the
   declaration and `mutual` handlers run the native handler with no changed
   options, no stored entry and no record. A module compiled this way has the
   same declarations (types and values) and the same compiler output as one
   compiled without the collector module. A module that does not import the
   collector module has no handler of ours at all (decision 1).
2. **Named proof bodies are measured, including mutual blocks.** (Owner decision, 2026-10-25.) A completed
   record exists for each named theorem and each named definition whose value is a
   proof (its type is a proposition), in ordinary declarations and in native
   `mutual` blocks (all peers). A definition whose type is not a proposition
   has no proof record; it is neither labeled as a proof nor listed as
   unmeasured. Each record says which of the two kinds it is. Embedded proofs and
   generated helpers get no separate record, and the report says so in its
   header. A theorem inside `namespace` or `section`, and a `where` or `let rec`
   body, belong to their parent record.
3. **Identity is stable or marked.** (Owner decision, 2026-10-25.) A record is identified by module name and
   qualified declaration name, with no absolute path. Private and anonymous
   (`example`) declarations are recorded with a class that says that their identity
   changes with edits. The report lists them in their own section, and the
   comparison does not use them (ADR 0017, accepted contract).
4. **A record carries what makes it comparable.** (Coordinator decision, 2026-10-25.) Compiler version, the boundary
   scheme including the async mode (`Elab.async`), the unit, the exact count and the
   status (`completed`, `failed`, `precision-unavailable`). Counts that Lean's
   `Float` trace endpoints cannot represent exactly become `precision-unavailable`.
5. **Usable only after a successful compile.** (Coordinator decision, 2026-10-25.) Records come from the compiled
   module file. A module with an error has no compiled file, and the tool reports
   that and exits 2. The tool does not build. A module whose Lean file changed
   after its compiled file was made is reported as stale, not as measured
   (decision 4). The README says to run the tool after a successful `lake build`;
   a failed build caused by something other than that file's text (an import or a
   compiler option) is not detected.
6. **Missing coverage is explicit.** (Coordinator decision, 2026-10-25.) For every library module that the tool
   reads, each named theorem that has no completed record is listed as
   `unmeasured`, including every theorem of a module compiled without
   collection. Lean-generated helper declarations are not listed. A proof-valued
   definition is listed only when collection saw it; the report states this
   limit (decision 6).
7. **Measurement does not change the claim or the output.** An instrumented
   compile has the same declaration types and values, the same messages, and no new
   axiom (`sorryAx`, `ofReduceBool`, native decision) as a native compile. The native
   trace line does not appear in the output. Compiler errors stay errors, with their
   native text. The one exception is resource exhaustion that the instrumentation
   itself causes: a proof near `maxHeartbeats` can exceed it (outcome 12).
8. **Native async stays on.** Collection does not set `Elab.async`. Both async
   and sync compiles give attributed records: an expensive proof after a cheap
   one, and before it, shows its growth on its own theorem only.
9. **Other handlers and the S5 check still work.** The two handlers keep
   Lean's incremental elaboration (the `incremental` tag). With the collector
   imported, a command that another `declaration` handler wants to elaborate is
   still elaborated by that handler, whichever handler was registered first
   (decision 5). The S5 automatic check gives the same errors, suggestions and
   code actions on the same file with collection on and off, and its search work is
   not part of any body record.
10. **`--costs` reports.** `lake exe belay-sql-check --costs [--library NAME]`
    prints, for each selected library, its own modules' proof records in a fixed
    order (module, then declaration), the unmeasured theorems, the
    unstable-identity section, a coverage note, the unit and the compiler and
    scheme of the data. `--json` prints the same data as a baseline file.
    Counts are shown as exact decimals of budget units (for example `31.765`).
    Without `--costs` the checker behaves as before. One invocation has one
    mode (decision 3).
11. **CI compares to a baseline with a user-set allowance.** With
    `--baseline FILE --allowance UNITS` (units are Lean budget units, an exact
    decimal with at most three places), the tool compares only compatible records
    (same compiler, scheme and unit) matched by module and declaration. It reports
    growth when `current > baseline + allowance`, using integers and no rounding. It
    lists, in separate sections and never as zero: incompatible records, new
    entries, baseline entries with no current completed record (absent, failed,
    unmeasured or precision-unavailable, with the cause), and removed or renamed
    declarations (a removal plus a new entry). It never writes the baseline. A
    missing allowance, an unreadable or malformed baseline, and a negative or
    too precise allowance are errors that say what to change. There is no numeric
    default. Exit codes follow decision 3.
12. **The guide's disclosures are in the user documentation.** The package
    README section tells how to turn collection on, what the boundary includes
    and excludes, that counts vary by a few units between runs and with source
    order and async mode, that instrumentation adds heartbeats (a measured
    sample from the production collector, not a bound) and can push a proof that
    is near `maxHeartbeats` over it, that a Lean upgrade makes a baseline
    incompatible, and how to create a baseline.
13. **The prototype is replaced.** The test-only collector, its reader commands and
    its tests are removed or rewritten onto the production code, and callers are
    updated. `docs/s7-proof-cost-findings.md` stays as the historical record and
    gets a short section that points to the production result. The ADR sentence
    "Production collection and native mutual coverage remain implementation
    work" is updated when the work is done.

## Test suite

All tests have finite subprocess timeouts, test our code (the collector, the
checker and the comparison), and use the Nix `surface` suite. Tests do not assert
exact counts across compiles; they assert relations (a costly proof is more than
ten times a cheap one; growth is detected; a count is an integer).

- **Collection** (`tests/surface_proof_cost_collect_test.py`, with Lean fixtures
  under `tests/surface/`; compiles with the installed `lean` and no Lake build):
  - attribution in both orders, in async and sync mode, with a changed proof
    showing growth only on its own theorem (outcomes 4, 8);
  - a coverage table: tactic and term theorem, proof-valued definition, predicate
    definition (no record), namespaced, private and anonymous (class marked),
    recursive theorem and embedded proof (parent only, no helper record),
    `mutual` with theorem peers (and with proof-valued definition peers, where
    Lean accepts them) (outcomes 2, 3);
  - one record for each declaration, also for declarations that a macro or a
    nested `elabCommand` expands to (no duplicate identities);
  - disabled bypass: option off or collector not imported, same declaration
    snapshot and output, no records, and no handler state (outcome 1);
  - output cleanliness and no new axiom (outcome 7); a failed body gives a
    compile error and no compiled file (outcome 5);
  - the `incremental` tag on both handlers, and a fixture third-party
    `declaration` handler registered before and after ours (outcome 9).
- **S5 coexistence** (`tests/surface_proof_cost_automatic_test.py`, importing
  `Belay`): a false SQL statement and a true one give the same diagnostics and
  suggestions with collection on and off, and a body whose automatic check costs
  far more than the proof has a record near the check-off record (outcome 9).
- **Report and comparison** (`tests/surface_proof_cost_report_test.py`, real Lake
  consumer package built from the installed layout, as in
  `tests/surface_sql_check_test.py`): `--costs` output and `--json` for a
  two-library package; a module without collection lists its theorems as
  unmeasured; a repeat run gives identical bytes; the baseline file and the build
  artifacts are untouched; growth at exactly `baseline + allowance` passes and
  one internal unit more fails; allowance parsing (`0`, `2.5`, `0.001`, `0.0001`
  rejected, negative rejected, missing rejected); an edited baseline with another
  compiler or scheme is incompatible and not a regression; new, removed, failed
  and unmeasured entries are separate; a malformed baseline; a stale compiled file
  after a failed recompile (outcome 5). The plain `--library` mode keeps its tests.
- **Pure comparison** (a Lean fixture with `#guard`s under `tests/surface/`):
  the inequality at its boundary, exact decimal conversion, ordering and
  classification, on the pure module without Lake.
- **Layers** (`tests/surface_layers_test.py`): the collector module imports only
  Lean and our own modules; Lake is imported only by checker modules.
- **Overhead sample** (in the collection test): the three surface proof patterns
  of the prototype, compiled with and without the production collector. The
  window counts go to JUnit properties for the README. The test asserts that
  the records exist, not a bound.

Each coherent commit has focused checks and an independent review. A part ends
with post-review `just test-full` and `just verdict`; the task end adds
`just test-nix` and `just test-scheduled-checks`. The owner's rule is that
the mutant suites run in CI and never locally; `CLAUDE.md` names
`just test-scheduled` for this point, which also runs them (see the report on
this task). Only Nix results are evidence. After an edit of `BelaySqlCheck.lean` run `lake build belay-sql-check`
as well, because `just dev-build` does not build it. Frozen predictions, the
judge and its lock stay unchanged.

Part 1 is outcomes 1-9 and 13 (collector, records, tests, prototype removed).
Part 2 is outcomes 10-12 (checker, comparison, documentation, end-to-end).

## Tricky points

- **Hook design.** Delegating to `elabDeclaration` directly, as the prototype
  does, would hide any other `declaration` handler registered earlier than ours.
  The handler can instead find the later entries of
  `commandElabAttribute.getEntries` for the syntax kind and try them in order,
  restoring state on `unsupportedSyntax` (how Lean's `elabCommandUsing` works).
  Handlers nest: `elabCommand` inside a handler runs the hook again, so the
  record set must not hold one body twice.
- **Measuring.** The native `Elab.definition.value` trace nodes (`elabFunValues`
  in `Lean/Elab/MutualDef.lean`) are the boundary. Enabling them makes Lean print
  them; the output must be restored. The trace label is a formatted message, not a `Name`
  (the prototype reads its text). Take the canonical `Name` of each declaration from
  the command's own declaration information and correlate it with the label, so
  that private and anonymous names stay exact.
  Proof tasks finish after the command returns, so the record set is completed
  at export (`Pending.finish` in the prototype) and the compiled file exists only
  for a successful compile.
- **Proof-valued definitions.** Classify by the declaration's type being a
  proposition. `def p : Prop := True` is a definition of a proposition, not a proof.
- **Unmeasured inventory.** Module data lists the theorems of a compiled module
  without our hook. Lean also stores generated declarations (`_proof_n`, equation
  lemmas, matcher helpers, `recursive._f`); the rule that excludes them must not
  exclude a user's `theorem _name`. The S5 `Check.statements` shows one way to
  recognize names that a command declares; it belongs to S5 and stays read-only.
- **Stale compiled files.** Lake can leave the previous compiled file when a
  recompile fails. Decision 4 says what the tool can notice.
- **Checker size and layers.** `BelaySqlCheck.lean` is near 200 lines. Put pure
  parts (record, report, comparison) in Lake-free library modules that the
  checker imports, as `SqlCheckReport` does. A second Lake-importing module needs
  a deliberate change of layer rule 6.
- **Option scope.** A library-wide setting needs the `weak.` prefix: Lean rejects a
  command-line option that no imported module declares, and a module that does
  not import the collector does not declare ours. Test the lakefile form the README shows.
- **Compatibility.** The scheme names the compiler version, so each Lean upgrade
  makes old baselines incompatible by design (`CLAUDE.md`, "Lean maintenance").
  Say so; do not add migration code.
- **Self-measurement.** The collector's own later declarations can be measured
  when they follow the handler's definition in the same module. Keep the handlers
  last in their module or accept the records; do not special-case.

## Ownership

May change:

- New Lake-free modules `packages/belay/Belay/Sqlite/ProofCost*.lean` (records,
  collection, hook, pure comparison and report), each under 200 lines with checked
  Verso docstrings.
- `packages/belay/BelaySqlCheck.lean` (the `--costs` mode), the module list of
  `packages/belay/lakefile.lean` (append only), and rule 6 of
  `tests/surface_layers_test.py` only if a second checker module is needed.
- `packages/belay/README.md` (a "Proof costs" section), `docs/s7-proof-cost-findings.md`
  (a production section), the one ADR 0017 sentence in outcome 13, and the plans of
  this task.
- The prototype fixtures `tests/surface/ProofCost*.lean`, `tests/proof_cost_test.py`
  and `tests/proof_cost_support.py` (rewritten or removed), the new tests above, and
  registration lines in `tests/nix_suites.json` and `build-support/tests.nix`.

Must not change: the model package, `judge/`, the corpora, `integrity/judge.lock.json`,
the S6 assertion and before-context modules, the editor modules (`SqlTable*`,
`SqlStatementContexts`, `SqlOrderWarnings`, `SqlEditorInfo`), the S5 modules
(`Check*`, `Sampling*`, `ReplayScript`, `SqlAutomatic`), and the barrel
`Belay/Sqlite.lean` under decision 1 (the collector is not part of `import Belay`).
Shared registration files get minimal append-only edits.

## Decisions (answered 2026-10-25)

Decisions 2 and 3 are the owner's. Decisions 1, 4, 5 and 6 are the coordinator's;
each takes the recommended option. The alternative that was not taken stays
listed to show what the outcome excludes.

1. **How a user installs the collector.** Recommended: a separate module that
   `import Belay` does not import, plus the option (outcomes 1, 9). Alternative:
   install the handlers for every user of `Belay` and rely on the bypass.
2. **Baseline file.** Recommended: the `--json` report is the baseline; the user
   saves it and the tool never writes it (outcome 11). Alternative: a separate
   `--write-baseline` mode.
3. **Failing conditions and modes.** Recommended: exit 1 for growth, for a
   baseline entry without a current completed record and for a failed record;
   exit 2 for incompatible data, unreadable libraries and usage errors; new
   entries are reported with exit 0. `--costs` runs alone, and the freshness
   check stays a separate invocation (outcomes 10, 11). Alternative: one run
   does both and combines the codes.
4. **Stale compiled files.** Recommended: each record stores a hash of its
   module's source text, and the tool reports a module whose file changed as
   stale; this detects source edits only, and the README tells users to run the
   tool after a successful `lake build` (outcome 5). Alternative: no hash, and the
   README instruction alone.
5. **Other `declaration` handlers.** Recommended: the chain delegation in
   "Tricky points" (outcome 9). Alternative: delegate to `elabDeclaration` only and
   document that earlier third-party handlers are bypassed when collection is
   on.
6. **Unmeasured inventory.** Recommended: theorems from module data, and
   proof-valued definitions only when collection saw them (outcome 6).
   Alternative: load each module's environment in the checker to classify every
   definition, which makes the checker heavier.
