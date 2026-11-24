# Exact steps for writes with rules or RETURNING

Created 2026-11-24. Status OPEN.

[Task](20261124-write-mode-rules.task.md) ·
[ADR 0033](../docs/adr/adr-0033-exact-step-rules.md)

The first kind under owner decision 2 is INSERT with write rules. Its
success uses the key run's changes or its written rows, and its failure
takes the same transaction path as the other writes. The model's support
check combines the plain-write checks with the key run's readiness.

## First INSERT with write rules

Measured before implementing another slice 7 kind. The no-RETURNING
equation in InsertWithRules.lean has 67 scc code lines, its model import
adds one, and InsertWithRulesClaim.lean adds 18 client lines. The latter
checks both output cases on an arbitrary valid database and modeled send.
There are no new surface declarations, projections or tactic branches.
The selected Lean tree goes from 99,064 to 99,150 lines (+86), including
59,460 to 59,528 model and 21,558 to 21,576 tests. The pytest registration,
build declarations and plan prose are outside the simplification counter.

The first-kind pytest check is test_insert_with_rules_reports_its_count_or_error
in surface_schema_script_test.py. Its new client fixture elaborated in 2.14 s
(lower of two runs). Review requested the resolution premise and universally
quantified inputs in the rule docstring, and the name of this test in the log.

The named pytest checks of the remaining modes are
test_all_returning_and_program_write_modes and test_replaced_write_mode_laws.
The key-program and RETURNING equations expose each successful projection,
failure, connection and source alternative. The common proof obligations
for clocks, counters and one ordinary write are in WriteRuleProofs.

The remaining write equations cover INSERT, UPSERT, UPDATE and DELETE
with returned columns, every write-program mode of those constructors,
INSERT SELECT with returned columns or a program, and DROP with a program.
The three client fixtures report only logical axioms. ProgramWriteClaims,
ReturningWriteClaims and SourceWriteClaims are new. Their local D11
elaboration times are 4.93, 3.13 and 3.22 seconds respectively.

ReplacedProgramDrop witnesses runScriptStep_drop_keys and
runScriptStep_drop_failed. ReplacedProductionSuccess witnesses
runScriptStep_insertSelect_ok and runScriptStep_insertSelect_success.
ReplacedWriteChoices witnesses the Output.ofStep and runScriptStep
no-choice laws for UPDATE and DELETE. The capability groups are script
execution, write effects and query-source writes. SchemaDropExamples and
InsertSelectExamples now use the exact rules. ReplacedUpdateSendLaws and
ReplacedDeleteSendLaws use the nonquery projection. The group frame for
INSERT SELECT still serves callers with varying RETURNING and program modes.
The D11 count before the final stack rebase is 100,275 selected Lean lines,
including 60,287 model, 14,339 surface and 21,956 test lines.
