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
