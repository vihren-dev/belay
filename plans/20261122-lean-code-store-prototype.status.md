# Status: a prototype of the Lean code store extractor

Date: 2026-11-22. Status: DONE (2026-11-22). The owner questions are in the findings record; the deferred review
findings are in the review records `reviews/20261122T132942Z-c530101e`,
`reviews/20261122T135558Z-7e390e7e` and `reviews/20261122T141007Z-ec809ab0`.
Task: [20261122-lean-code-store-prototype.task.md](20261122-lean-code-store-prototype.task.md).
Specification: [the Lean code store](../docs/records/spec-lean-code-store.md),
[ADR 0032](../docs/adr/adr-0032-lean-code-store.md).

## Source files

- `experiments/lean-code-store/extractor/`: the Lean fact reader (`lean-code-store-facts`), one
  process for each module, in the environment of the module and its imports.
- `experiments/lean-code-store/lean_code_store/`: keys (`keys.py`), folding rules (`folding.py`), resolution of parents (`resolve.py`),
  user of a mention (`mentions.py`), rows (`rows.py`), local row files (`store.py`), the run
  (`run.py`, `inputs.py`), the `clickhouse-local` load and query (`clickhouse.py`), the
  tables of the findings record (`report.py`).
- `experiments/lean-code-store/fixture/`: the fixture package and `expected-rows.json`.

## Tests

`python3 -m pytest -c experiments/lean-code-store/pytest.ini experiments/lean-code-store/tests`:
unit tests of keys, folding, resolution, text cuts and mention users, and the fixture test (needs Lean and
Lake; builds the fixture copy, compares rows, checks the second run and an edit). The
experiment has its own `pytest.ini`, so the repository's upload of test observations is not
loaded.

## Progress

- 2026-11-22: task file written. No code.
- 2026-11-22: first prototype. It implements the rules of "Generated constants" as the
  specification writes them, for the constants of the selected modules. For a target outside
  the selection it applies only rules 1 and 5: rules 2 and 3 need the ranges of all constants
  of the target's file, which the prototype does not read for Lean's library. Input: the Nix
  packages of `just theorem-dependencies` for this revision. Local measurement, not evidence:
  1,617 modules in 196 s; a second run extracts 0 files in 4 s; with the rules as written, no
  rule decides 13,108 constants. The report of this commit does not name a generated constant
  whose parents end in a reported constant; the next commit names them (161 in a run of the
  same rules). The next commits record this and correct the rules.
- 2026-11-22: review fixes: a generated constant whose parents end in a reported constant is
  reported with that cause; tests for a changed build product, an indented `deriving instance`
  command, a generated target in Lean's library (`Nat.casesOn`), and the `clickhouse-local`
  load and query.
- 2026-11-22: review fixes: the text of a `deriving instance` command ends at the last type of
  its `for` list (a regular expression; it was correct only for the tested multiline cases and
  failed for quoted names and comments, and the next entry replaces it); extractor version 2, so the store extracts again the file versions of
  version 1; the fixture uses `Prod.mk` and `Prod.fst` as the only source of `Prod`; the query
  test has a target with two users.
- 2026-11-22: review fixes: the fact reader takes the range of a `deriving instance` command
  from Lean's own command parser (`extractor/LeanCodeStore/Commands.lean`). The fixture tests
  a comment in the `for` list; the next entry covers the other comment cases. The version test fills the store with version 1 and requires the
  current version to extract all five modules again.
- 2026-11-22: review fixes (round 4): the parser reads the header and then each command in
  order, so text in comments is skipped as Lean's front end skips it. The fixture tests a line
  comment after `deriving instance`, and a block comment with a line that starts with
  `deriving instance` before an ordinary instance and a later real command. Extractor version
  3. Known limit, deferred: the parser uses the module's final environment, so a syntax
  extension that the file declares after the command can change how it parses. Review rounds
  1 to 4 all had "must" findings, rounds 2 to 4 on the text of `deriving instance` commands; the
  review loop on this subject stops here and the report names it.
- 2026-11-22: the stack is rebased on the specification revision that widened rule 5 (any
  final component). The prototype implements that rule and three corrections that the next
  commit adds to the specification: rule 5 also after the removal of the private prefix; a
  constant with macro scopes and a range folds into the one constant without macro scopes of
  its range, else it is reported; an instance of an unparsed `deriving instance` command is
  reported. `lean_code_store/resolve.py` now holds the resolver. Extractor version 4. Local
  run of the matched build, not evidence: an edit of one file of the conformance package in a
  writable copy extracts 7 file versions, the file and its 6 importers, which are the modules
  that Lake rebuilt.
- 2026-11-22: review fixes of the rule corrections: the fact reader gives
  `Name.hasMacroScopes` of each name, and the macro-scope rule uses it; an instance is
  reported as an unparsed `deriving instance` instance only when its full range is its
  selection range, so a `def` that `attribute [instance]` makes an instance stays a
  declaration (fixture `inhabitedPoint`). Extractor version 5. The specification states three
  points as open: `register_simp_attr` gives two declarations with one text, a later syntax
  extension can change the parsed command boundaries, and the store of a relationship whose
  target is reported.
- 2026-11-22: review fixes: an unparsed `deriving instance` instance also needs a text that
  is one name, so a macro instance with equal ranges stays a declaration; the specification
  says that a mention with a reported container gets its user by the range rule; a test of a
  quoted name that contains `._@.` as the only parent of a macro-scoped constant.
- 2026-11-22: `lean_code_store/report.py` prints the tables of the findings record from the
  facts, the store and the query result (`tests/test_report.py`). The review loop of the
  folding-rule commits stopped after four rounds with new "must" findings; the five findings
  of review `20261122T135558Z-7e390e7e` are deferred for the owner. The findings record names
  that review and summarizes its findings 2 and 3 (macro instance, quoted class name); it
  notes that extractor version 6 met finding 1; findings 4 and 5 (a test docstring, a test
  of the `macroScopes` diagnostic) are only in the review record.
- 2026-11-22: review fixes of the report: the store keeps the decision of each constant in
  `counts.json`, and the report reads the decisions, causes and counts of the requested
  snapshot's file versions only, so it needs no facts directory. A test runs `report.main` on
  a small store. Extractor version 6; the version test writes with the current code under
  the version 5 key prefix and checks that version 6 extracts all modules again.
- 2026-11-22: review fixes of the report tests: the report refuses a snapshot without its
  `snapshots` row; the test has two snapshots and long texts; the fixture test reads back
  stored decisions of `Fixture.Types`.
- 2026-11-22: `docs/records/lean-code-store-prototype-findings.md`: the counts of a full run
  of version 6 (local, not evidence), the sample of 20 candidates read against the source
  (15 true, 5 false), the wrong statements of the specification and the ADR, and the owner
  questions. The review loop of the report commits stopped after four rounds; the findings
  of review `20261122T141007Z-ec809ab0` are deferred.
- 2026-11-22: review fixes of the findings record: the sources of the tables, the groups of
  the reported constants by module, the extractor version of the edit run, the opaque and
  `where` candidates, the limit of "true" candidates, the ADR corrections as pending, the
  partial check `isAutoDeclOrPrivate_Internal`, and 15 stored rows of reported targets.
- 2026-11-22: review fixes of the findings record: the `match_on_same_ctor` constants of
  `BEq` and `DecidableEq`, the `SqlSelectRule` functions without a written parent, and the
  limit of the source search.
- 2026-11-22: ADR 0032: D6 states the private-prefix part of the name rule, and "Not
  decided here" refers to the prototype measurement; the specification links the findings
  record.
- 2026-11-22: DONE, with these exceptions and open points:
  - The rule 1 statement of the specification is not corrected: rule 1 says that Lean's
    tables give the "other constants" of a type, but `ctorIdx`, `injEq`, `sizeOf_spec` and
    `noConfusionType` are in no table and rule 5 decides them (findings record, wrong
    statement 8). Resolved later: commit `b164b5daa6de` corrects rule 1.
  - Two review-fix commits, `de015deec265` and `7e390e7ed528`, change the specification and
    the extractor together, so they do not follow the separate-commit rule for
    specification corrections.
  - Three review loops stopped after four rounds with new "must" findings: the text of
    `deriving instance` commands (deferred: a syntax extension that the file declares after
    the command, review `c530101e`), the folding rules (review `7e390e7e`) and the
    prototype report (review `ec809ab0`).
- 2026-11-22: review fixes of the rule 1 correction: rule 1 reads Lean's auxiliary-recursor
  tag and not `isAuxRecursor`, which also accepts `Eq.ndrec`, `Eq.ndrec_symm` and
  `Eq.ndrecOn` by name. Extractor version 7; the fixture rows now keep five `body`
  references to `Eq.ndrec`. The version test writes rows with the current extractor under
  version 6 file keys and checks that version 7 extracts all five modules again. The local
  measurements of version 7 are in the findings record. Tests: `python3 -m pytest -c
  pytest.ini tests` in `experiments/lean-code-store` (22 passed).

