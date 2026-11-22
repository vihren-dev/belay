# Findings of the Lean code store prototype

Date: 2026-11-22.
Status: findings of a local prototype run. The results are local: no check accepted them,
and they are not evidence in the sense of ADR 0011 and ADR 0020.
Audience: designers and reviewers.
Used by: [ADR 0032](../adr/adr-0032-lean-code-store.md),
[specification](spec-lean-code-store.md).
Task: [`plans/20261122-lean-code-store-prototype.task.md`](../../plans/20261122-lean-code-store-prototype.task.md).

## What ran

The prototype is in `experiments/lean-code-store/`. A Lean fact reader
(`extractor/`, one process for each module) reads the compiled environment of each module.
Python code applies the rules of "Generated constants", reads the `.ilean` usages, and
writes the rows of the six tables as local JSON-lines files. `lean_code_store.clickhouse`
loads them into `clickhouse-local` 26.5 with the DDL of the specification and runs the
single-use query of the specification. No ClickHouse server was used.

Input: the Nix packages of `just theorem-dependencies` for this revision (7 min 43 s), the
four library trees of the default selection (`belay-sqlite-model`, `belay-sqlite-text`,
`belay`, `verifier-conformance`), 1,617 modules, Lean 4.34.1. Extractor version
`lean-code-store-prototype-6`. The rules are those of the specification after the
corrections of this task.

How to run it is in the module docstring of `lean_code_store/run.py`. Sources of the tables:
the decisions, the reported constants, the mention users and the candidates come from
`lean_code_store/report.py --store STORE --snapshot ID --candidates FILE`; the row counts
come from `lean_code_store/clickhouse.py`, which also writes the candidates file; the times
and the extracted counts come from the summary that `lean_code_store/run.py` prints. Two full
runs, with extractor versions 5 and 6, gave the same counts. The tests are
`python3 -m pytest -c experiments/lean-code-store/pytest.ini experiments/lean-code-store/tests`.

## Decisions of the rules

40,877 constants of the selected modules.

| Decision | Count | Examples |
| --- | ---: | --- |
| Rule 1, generated (Lean's tables) | 5,499 | `Translation.NameRange.casesOn`, `NameRange.begins` |
| Rule 2, generated (`deriving` clause) | 853 | `instBEqSourceState`, `instBEqSourceState.beq` |
| Rule 3, declaration (instance) | 296 | `Translation.instInhabitedParseNode`, `Model.instFromJsonRow` |
| Rule 3, generated (helper of a `deriving instance` instance) | 184 | `Model.instFromJsonRow.fromJson` |
| Rule 4, generated (macro scopes, one constant of the range) | 20 | `initFn._@.…SqlFileLoad…` into `sqlPackageRootOption` |
| Rule 4, declaration | 7,368 | `Belay.Sqlite.dbBangTerm` |
| Rule 5, generated | 17,245 | `NameRange._sizeOf_1`, `NameRange.add.match_1`, `T.ctorIdx`, `T.mk.injEq` |
| Rule 5, generated after removal of the private prefix | 9,259 | `_private.….Grammar.Located.0.….Span.leaves.match_1.eq_1` |
| Reported | 153 | see below |

Rule 2 decided only instances of the classes of the `deriving` clauses (`Repr`,
`DecidableEq`, `BEq`, `Inhabited`, `FromJson`, `ToJson`, `Hashable`) and their helpers.
Each of the 186 instances of a `deriving instance` command got its command range from
Lean's parser; no instance was reported as unparsed.

### Reported constants, by cause

| Cause | Count | Examples |
| --- | ---: | --- |
| No rule: `_sparseCasesOn_N` with no name before it | 63 | `_private.Belay.Sqlite.Model.Programs.Clock.ClockExamples.0._sparseCasesOn_41` |
| No rule: `match_N` with no name before it | 52 | `_private.Belay.Sqlite.Model.Frontend.Codecs.StatementExamples.0.match_6` |
| No rule: macro scopes and no range | 14 | `Model.ExecutionError.match_on_same_ctor._@.…._hyg.44` |
| Macro scopes, several constants with the same range | 20 | `initFn._@.…StatementAttr…`, `ext._@.…StatementAttr…` |
| Macro scopes, no constant with the same range | 3 | `initFn._@.…SqlSelectRule…` |
| Helper of rule 3 with several candidates | 1 | `Belay.Sqlite.Model.instToExprExpr_1.toExpr_2` |

Causes:

- The 115 match and `_sparseCasesOn` functions have a private name in which the function
  name directly follows `_private.<module>.0`, with no declaration name between them. They come from commands that are not declarations, for example the
  `#guard` commands of `Schema/Ddl/DropColumnExamples.lean`. 113 are in `*Examples`
  modules; the other two are `_private.….Values.Json.JsonApply.0.match_7` and
  `_private.….Schema.Dispatch.QueryOutputs.0.match_3`. The command has no declaration, so
  the function has no parent. Reporting them meets the requirement of the specification.
- Of the 14 constants with macro scopes and no range, 10 are `match_on_same_ctor` constants
  of derived instances, 8 of `DecidableEq` and 2 of `BEq` (for `Syntax.Expr` and
  `Syntax.Statement`), for example `Model.ExecutionError.match_on_same_ctor._@…` and
  constants in `Shared/Resolved/ResolvedExprForm.lean`. The other 4 are match and
  `_sparseCasesOn` functions of the `initialize` command of
  `Queries/Automation/SqlSelectRule.lean` (`….initFn.match_1._@…`). For each, the name
  without its final component ends in macro scopes and is not a constant.
- The 20 macro-scoped constants with several partners come from commands that declare two
  constants without macro scopes with one range: 4 in `Frontend/Codecs/StatementAttr.lean`,
  8 in `TracedAttr.lean`, 4 in `Queries/Automation/SqlSelectRule.lean` and 4 in
  `SqlSimp.lean`. For example, `Parser.Attr.statement_arms` and
  `Parser.Attr.statement_arms_proc` have the same range. Rule 4 makes both declarations with
  the same text.
- 12 more generated constants are reported because their parents end in a reported
  constant: 10 `match_on_same_ctor.het._@…`, and `instToExprExpr_1.toExpr_2._unsafe_rec` and
  `….toExpr_2.match_1`.

With the rule 5 of the specification revision on which this task started (only final
components `_…`, `match_N`, `eq_N`, `eq_def`), no rule decided 13,108 constants, and 161
generated constants had a reported parent. The largest groups were the private equation
lemmas `_private.<user>.0.<f>.match_N.eq_N` (7,592), `splitter` (1,652), `sizeOf_spec`
(1,103), `inj` and `injEq` (600 each), `ctorIdx` and `noConfusionType` (370 each).

## Mention users

| Source of the user | Usages |
| --- | ---: |
| The `.ilean` container, after folding | 157,200 |
| The one smallest declaration range | 11,363 |
| None (empty `user_name`) | 21,043 |
| Not a relationship: the key names no constant | 17,437 |

The keys that name no constant are options, docstring roles and other names; their module
in the key is the current module. The selected trees contain no `sql_module` user.

## Rows and time

| Table | Rows written | Rows after `FINAL` |
| --- | ---: | ---: |
| `files` | 1,617 | 1,617 |
| `entities` | 7,664 | 7,664 |
| `entity_texts` | 7,589 | 7,556 |
| `entity_references` | 439,498 | 439,498 |
| `snapshot_files` | 1,617 for each snapshot | 3,234 for two snapshots |
| `snapshots` | 1 for each run | 2 |

| Run | File versions extracted | Wall time |
| --- | ---: | ---: |
| First run | 1,617 | 199 s: fact reader 184 s with 4 processes (sum 732 s, at most 1.4 s for one module), keys 3 s, rows 12 s |
| Second run, no change | 0 | 3.8 s, nearly all for the keys |
| After an edit of `VerifierConformance/Tooling/Conformance/Classify.lean` in a writable copy of the package, and `lake build` there (extractor version 4, before the macro-scope rule, on the store of its own first run) | 7 | 5.5 s |

The 7 file versions are the edited file and its 6 importers. They are the 7 modules that
Lake rebuilt. The load into `clickhouse-local` and the query took 1.4 s.

## Declarations with one user

The query gave 2,285 candidates.

| Target kind | `used_in_a_type` = 0 | `used_in_a_type` = 1 |
| --- | ---: | ---: |
| theorem | 1,148 | 2 |
| definition | 939 | 44 |
| instance | 121 | 0 |
| opaque | 27 | 0 |
| inductive | 0 | 2 |
| structure | 1 | 1 |

Of the 121 instance candidates, 97 are instances of `deriving instance` commands. The 27
opaque candidates are 11 `partial def` declarations, 1 `where` function of a partial
definition (`Run.runGoal.runSend`), 5 `opaque` declarations (for example
`ParserLibrary.metadata`), and 10 constants whose text contains `initialize` or `register`,
such as `Belay.Sqlite.parserMetadata`. 14 candidates are `where` functions whose only user
is their parent; `Run.runGoal.closesBySelect` is a `where` function whose only user is its
sibling `Run.runGoal.runRead`.

A sample of 20 candidates, the first 20 by the SHA-256 of the name, read against the
source and a search of all Lean files of the repository. "True" means: the source and the
search show no other user. Uses that the build products do not record can still exist and
can be missed by the search too: kernel unfolding leaves no name in the text, and a name in
a tactic quotation is in the text but Lean can omit its usage from the build products, so
the search finds it only when it uses the same short name. The specification names this
limit.

| # | Candidate | Only user | Result |
| ---: | --- | --- | --- |
| 1 | `Translation.numberToken.named` | `numberToken` | True; a `where` function |
| 2 | `Model.Json.groupMembers` | `Json.groupObject` | True |
| 3 | `Model.instToJsonTableConstraint` | `instToJsonStatement` | False: derived instance |
| 4 | `Script.observeTwoState_ordinary` | `Holds.inContextSince_iff_inContext` | True; the only use is a `{name}` reference in a docstring |
| 5 | `Json.renderFloat5Digits` | `Json.renderFloat5` | True |
| 6 | `Model.drop_resolveReferenceTraced` | `resolveSources_some` | False: `@[traced_drop]` attribute |
| 7 | `CatalogTable.columns_length_of_blankNames` | `Table.RowsWide.of_blankNames` | True |
| 8 | `Resolved.unhexBytes` | `Resolved.unhexValue` | True |
| 9 | `Translation.binaryForm` | `queryExpressionWith` | True |
| 10 | `Model.instToJsonRaiseKind` | `instToJsonExpr` | False: derived instance |
| 11 | `Sampling.touchedTargeted` | `Sampling.candidates` | False: also used in `tests/surface/Tooling/Tests/CandidateConstraints.lean` |
| 12 | `Model.maximumSecondFraction` | `parseSeconds` | True |
| 13 | `Catalog.findTable_isSome_set` | `Catalog.Valid.addColumn` | True |
| 14 | `Model.compoundCollations` | `resolveCompoundBodyTraced` | True |
| 15 | `Check.maxLiteralBytes` | `Check.checkDataSize` | True |
| 16 | `Translation.foreignKeyAction` | `Translation.actions` | True |
| 17 | `Resolved.roundDigitLimit` | `Resolved.roundValue` | True |
| 18 | `runStatement_createTable_keysUnique` | `runStatement_keysUnique` | True |
| 19 | `Model.instToExprSelectBody` | `instToExprStatement` | False: derived instance |
| 20 | `sendStatements_branch_resolveState` | `KeptRead.preserves` | True |

Under this limit, 15 are true candidates and 5 are false. Causes of the false candidates:

- A derived instance (3): instance resolution is the use, and the text is a `deriving
  instance` command that can also declare other instances, for example
  `deriving instance Lean.FromJson, Lean.ToJson for Syntax.ColumnDefinition,
  Syntax.TableConstraint`. Such an instance cannot be inlined.
- Attribute membership (1): 41 lemmas carry `@[traced_drop]`, and `simp only [traced_drop]`
  uses the set. The specification names this limit.
- A use outside the selection (1): the use is in the `tests/surface` tree, which is not in
  the default selection. The specification names this limit.

## Wrong statements of the specification and the ADR

Each statement with the declaration that shows it, and what this task changed. The
specification and the ADR were re-read before each change; the other session's revision
`vrnksnnsvpnm` had already widened rule 5 to any final component.

1. Rule 5 found no parent for an equation lemma that Lean generates in another module.
   `_private.Belay.Sqlite.Frontend.Grammar.Located.0.Belay.Sqlite.Translation.Span.leaves.match_1.eq_1`
   has the private prefix of the using module, so the name without its final component is
   not a constant (9,259 constants). Changed: rule 5 also uses the name without the
   private prefix. The ADR D6 summary of the rule still has the old text at this revision;
   the next commit changes it.
2. Rule 4 made generated constants declarations: `initFn._@.…SqlFileLoad…` has the range of
   the `initialize` command of `Belay.Sqlite.sqlPackageRootOption` (43 such constants).
   Changed: a constant with macro scopes (`Name.hasMacroScopes`) and a range folds into
   the one constant without macro scopes of its range, else it is reported.
3. "The extractor finds the command in the source text around the declaration range." A
   search of the text takes a comment for a command or stops at a comment inside the
   command; the fixture `experiments/lean-code-store/fixture/Fixture/Derive.lean` has both
   cases. Changed: the extractor parses the commands of the file with Lean's parser, and an
   instance with a name-only range and no parsed command is reported.
4. The status said that nothing was implemented and that the queries were not run.
   Changed. The ADR says that no measurement of the time exists; the next commit changes
   it to refer to this record.
5. The rule for mention users did not say that a usage of a type name in a `deriving
   instance` command has the empty user: no full range contains it, because the full range
   of such an instance is the class name. Changed: the specification states it.
6. The source table did not say that an `.ilean` key can name something that is not a
   constant. Changed: the specification states it.
7. Not changed, stated here: the specification names `Environment.isAutoDecl` of Batteries
   as a check of rule 5. Lean core 4.34.1 has `Lean.isAutoDeclOrPrivate_Internal` in
   `Lean/AutoDecl.lean`, which is true for many generated names and also for each private
   and macro-scoped name. It is a partial check only: it is false for
   `Belay.Sqlite.instInhabitedDiagnostic.default`, which has no range and which rule 5
   decides as generated. The fact reader gives it for each constant (`leanAutoDecl`).
8. Not changed, stated here: rule 1 says that Lean's tables give the "other constants" of a
   type. `ctorIdx`, `injEq`, `sizeOf_spec` and `noConfusionType` are in no table; rule 5
   decides them.

## Questions for the owner

1. A command that declares two constants without macro scopes with one range
   (`register_simp_attr` gives `X` and `X_proc`): which one is the written declaration?
   Today both are declarations with the same text, and the macro-scoped constants of the
   command are reported (20).
2. A constant whose name ends in macro scopes and has no range: should the rule remove the
   macro scopes and fold it? For the 10 `match_on_same_ctor._@…` constants of derived
   `DecidableEq` and `BEq` instances (and their 10 children), the parent would be the type.
   The 4 match functions in `SqlSelectRule.lean` belong to the macro-scoped `initFn` of an
   anonymous `initialize registerBuiltinAttribute` command; that `initFn` is itself reported,
   because no constant without macro scopes has its range, so these functions have no
   written parent even with such a rule.
3. How should the store keep a relationship whose target is reported? The prototype keeps
   the kernel name and module of the target: 21 relationships before the removal of
   duplicates, 15 stored rows.
4. Should a usage in a `deriving instance` command get the instances of the command as
   users? The instances of one command share the text of the command, but the range of each
   instance is only its class name. A type name after `for` is outside each of these
   ranges, so the range rule gives the empty user.
5. Should the single-use query leave out instances, or derived instances? They are 121 of
   2,285 candidates, and the sample had no true instance candidate.
6. Lean's parser reads a `deriving instance` command in the environment at the end of the
   module. A syntax extension that the file declares after the command can change the
   boundaries. Is this limit acceptable, or must the extractor elaborate the file again?
7. The review of the folding-rule commits stopped after four rounds in a row with new
   "must" findings (records `20261122T134252Z-0dc0b72f` to `20261122T135558Z-7e390e7e`).
   Deferred and not fixed: an instance of a one-token macro that has equal full and
   selection ranges and a name-only text; a quoted class name with a space (`«my class»`) in
   an unparsed command. (The third, a test that a store of an older version is extracted
   again, was met later by extractor version 6.) The review of the report commits also
   stopped after four rounds (`20261122T140329Z-b9dddadd` to `20261122T141007Z-ec809ab0`);
   its last findings are deferred: the report reads the entity texts before it checks that
   the snapshot is complete, and some tests do not separate two snapshots by counts.

## What was not verified

- No Nix check ran on the prototype. The fixture test builds the fixture with the local
  `lake` and Lean 4.34.1.
- The 20 candidates were read against the source; the other 2,265 were not.
- The decisions of the rules were not compared with Lean's own list of the constants that
  each command adds.
- The edit run used a writable copy of the conformance package and the Nix builds of the
  other packages; an edit in `belay-sqlite-model`, which all trees import, was not run.
- Third-party packages and Lean's library are not in the snapshot; their constants fold by
  rules 1 and 5 only.
