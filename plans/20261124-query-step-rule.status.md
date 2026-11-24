# The exact step of a query

Created 2026-11-24. Status OPEN.

[Task](20261124-query-step-rule.task.md) ·
[ADR 0033](../docs/adr/adr-0033-exact-step-rules.md)

The query rule can use the general output equation, the frame for queries
and preparation errors, and the data functions in QueryOutputOn. Checked
the order of faults and the possible-results normalization in Output.lean.

The syntax-only send rule stays. Its caller can supply a modeled premise
on an arbitrary connection, with no validity hypothesis and no resolution.
The common bridge requires validity. Visible SELECT uses the syntax entry
point, while an abstract statement resolving to a query uses the exact rule.
The new continuation proof covers every execution and each chosen output.
The two key-check witnesses restate runScriptStep_keyCheck_resolved and
runScriptStep_keyCheck_continues. SchemaSuccess reads the foreign-key rows
in its group proof. SelectOutcomeCases uses the query equation for a
missing clock. QuerySendClaims checks the continuation and trace on a
variable connection for every modeled outcome.

Independent review requested a precise statement of the selected-output projection,
the SELECT dispatch order, a smaller tactic module, exhaustive output cases and
fixture documentation. The revision covers all five findings.

Inventory of the earlier query claims found five more single-kind laws.
ReplacedQueryOutputs checks runScriptStep_simpleTable_output,
runScriptStep_select and runScriptStep_select_returnsResult with their
original hypotheses. ReplacedPragmaOutputs covers runScriptStep_keyCheck_empty
and runScriptStep_tableKeyCheck_empty. The readiness, possible-result and
foreign-key criteria now supply the data facts. CertifiedQueryOutputs,
CertifiedQueryCommutation and DerivedColumnReads use the exact query
equation and the checks on a calm scan. The proofs in SelectExecution and
SelectContextExecution and the ForeignKeyAtoms fixture use the general
output projection and the corresponding data facts. These cover query
results, program equivalence and foreign-key observations.

The former goal-shape test in S6AutoKindRuleCases now exercises the new
choice obligation directly: it recovers each selected output together
with its membership evidence. Review clarified the six scan checks and
the proof sketch, named the new witnesses in the test, and kept the
foreign-key fixture below 200 lines.

Owner decision 4 applies D12 to query rules. ReplacedContextRules
checks the original contracts of check_query_select_at and
check_query_select_faultless. Their replacement, Sql.check_query_of_step_rows,
takes a property of the actual output. Test test_context_cases checks
the read at the reached connection (A21) and the witnessed changes()
counter (A22), including native instances. The catalog caller now derives
the output from model data. Its public interface is the next migration.

[ADR 0033, owner decision 4](../docs/adr/adr-0033-exact-step-rules.md#owner-decisions) records the scope. The A21 and A22 fixtures each audit their own proofs.
