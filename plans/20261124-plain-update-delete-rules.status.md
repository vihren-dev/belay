# Exact steps for plain UPDATE and DELETE

Created 2026-11-24. Status OPEN.

[Task](20261124-plain-update-delete-rules.task.md) ·
[ADR 0033, D1–D11](../docs/adr/adr-0033-exact-step-rules.md) ·
[Pilot findings](../docs/records/statement-rule-pilot-findings.md)

## Starting revision

Slice 2 starts at fdcec52f, the head of PR #477, above the pilot in PR #476.
The Nix verdict at the starting revision is
`/nix/store/g78s7bipxgqzcmq06rbfmgvcr60jaicn-belay-verdict`.
Its report.json SHA-256 is
`cc8d3a2d6ffedff458ace5d6ce9b947f7feca8cceb176dbc35a3b766c1daf21b`.
Its counts.json SHA-256 is
`d8e2e1502df379445a40ebeb12812d30fbd6fb5c8be1372f295029cabdb90a6b`.

## Progress

2026-11-24. Traced the branches in StatementStep.lean and the send rules in
PlainUpdateStepRule.lean and PlainDeleteStepRule.lean. Both existing send
rules specialize subqueries to the empty list. The new rules cover all
subquery lists. The no-choice theorems in the model cover writes with
RETURNING and write rules too.

The slice adds the two registered rules and names the existing update effect
`updateOutcome`. Its success and error data facts serve the rule and the
group law. The equations cover every subquery list. The code removes
`plainUpdate_database`, `plainDelete_database` and the four surface laws
`Sql.check_send_plainUpdate`, `Sql.ifOk_send_plainUpdate`,
`Sql.check_send_plainDelete` and `Sql.ifOk_send_plainDelete`.

The following proofs now use a kind rule, the common send rule or `sql_run`.

| File | Proofs |
| --- | --- |
| DerivedColumnBackfillStep.lean | backfill_step |
| S6RulesEffects.lean | bump_stores_new_quantity, bump_succeeds_with_new_quantity |
| S6AutoEffects.lean | bump_stores_new_quantity_by_rules, bump_stores_new_quantity_by_sql_run |
| S6AutoPaths.lean | purge_empties_items |
| S6AutoShapes.lean | unreadable_statement_takes_the_rule_of_its_resolution |
| SelectContextCases.lean | big_after_delete |
| PurgeFrameClaims.lean | purge_frame |

ReplacedPlainWriteLaws, ReplacedUpdateSendLaws and ReplacedDeleteSendLaws
check the six former statements. They cover M03 (writes), M11 (clock and
counters) and S06 (program execution). The new client proof
`update_count_or_failure` covers both outcomes on an arbitrary valid
starting connection with a modeled UPDATE. The purge frame claim covers
arbitrary admitted databases with a stated purge site.

The affected tests are in surface_schema_script_test.py,
surface_s6_rules_test.py, surface_s6_automation_test.py,
surface_select_sources_test.py and surface_assertion_examples_test.py.

The starting Lean files match ee83eca7 in the pilot findings. The starting
counts are 59,191 model lines, 14,749 surface lines and 20,543 test lines
(98,176 total). At the implementation change, scc 3.7.0 counts 59,296
model lines, 14,575 surface lines and 20,745 test lines (98,309 total).
Both counts include 1,945 SQL text, 1,042 conformance, 134 documentation
tool and 572 other lines. The counts use the simplification goal's file set.

Review of fee371de found six documentation and tactic issues. The module
descriptions now state the resolution domain and distinguish the group
laws from exact rules. The three retention modules describe their subjects.
The tactic no longer assigns obsolete binder names to an outcome.
This removes one further surface line (14,574 surface, 98,308 total).

The review of c2df605a asked for the two outcome theorems to be named
as the facts about the update. The module description now does so.

Registered the two send witness roots and their imported model witness for Nix.

The Nix verdict after the change is
`/nix/store/ij7ch4wx5cbhrfw2bgqdqzka346kx288-belay-verdict`.
A recursive diff against the starting verdict found identical files.
The two retention fixture roots compile with the test target definitions
(8 tests passed). No mutant table changed.

Fixture elaboration times in seconds, the lower of two runs on this VM.
The end measurements use the implementation before the documentation and
fixture-manifest corrections.

| Changed sql_run fixture | Start | End |
| --- | ---: | ---: |
| S6AutoEffects | 2.05 | 2.81 |
| S6AutoPaths | 27.02 | 27.01 |
| S6AutoShapes | 0.91 | 1.01 |
| PurgeFrameClaims | 0.94 | 1.34 |
| SelectContextCases | 7.16 | 7.09 |

The default checker could no longer prove the concrete quantity UPDATE
in S6CheckPrograms within its first route allocation. It now retries an
exhausted route once if other routes left work in the same checker budget.
Interactive sql_auto retains its single pass. The affected suites are
surface_s6_check_programs_test, surface_s6_check_editor_test and
surface_s6_automation_test, including proof replay and bounded search.
Review moved the retry policy to Check.searchPasses and documented the default. The bounded interactive search test passed.
