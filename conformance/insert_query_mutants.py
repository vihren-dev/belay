"""Mutants of INSERT from a query: the orders of its source, streaming against collecting, the
transfer optimization and the output of a source failure (ADR 0019, D4, amended 2026-10-25)."""

from conformance.resolve_mutants import SQLITE

MUTANTS: dict[str, tuple[str, str, str]] = {
    "source_scan_order_only": (SQLITE + "SourceScanOrders.lean",
        "(scan :: (catalog.accessKeys position table.shape).map fun",
        "(scan :: ([] : List (List IndexKey × Option Resolved.Expr)).map fun"),
    "alternatives_dropped": (SQLITE + "InsertSelectRun.lean",
        "        alternatives := if rules.isNone then rest.map fun other => "
        "{ effect := other.effect, counts := other.counts, keyRows := other.keyRows }\n          else [] }",
        "        alternatives := [] }"),
    "source_always_streams": (SQLITE + "InsertSelectRun.lean",
        "    match query.productions context database !collects with",
        "    match query.productions context database true with"),
    "source_always_collects": (SQLITE + "InsertSelectRun.lean",
        "    match query.productions context database !collects with",
        "    match query.productions context database false with"),
    "returning_does_not_collect": (SQLITE + "InsertSelectRun.lean",
        "subqueries.any (·.readsTable target) || !returning.isEmpty ||",
        "subqueries.any (·.readsTable target) || false ||"),
    "transfer_rowids_ignored": (SQLITE + "InsertSelectRun.lean",
        "  | some source, .ok _ => (main.keyRows.getD []).map (·.rowid) == source",
        "  | some _, .ok _ => true"),
    "transfer_takes_any_projection": (SQLITE + "InsertSelectRun.lean",
        " &&\n        query.columns == (List.range table.shape.columns.length).map fun position => .scalar (.column position) then",
        " then"),
    "rules_with_two_orders": (SQLITE + "InsertSelectRun.lean",
        "(rules.isNone || others.isEmpty) &&",
        "true &&"),
    "source_failure_has_no_output": (SQLITE + "StatementOutput.lean",
        "    else if constraintFailure || overflow || functionFailure then\n      some ⟨returning.map (·.2), [], some (run.counts.changes.getD 0)⟩",
        "    else if constraintFailure then\n      some ⟨returning.map (·.2), [], some (run.counts.changes.getD 0)⟩"),
}
"""One exact change per mutant; each measurement builds only its changed classifier closure."""

TARGETS: dict[str, tuple[str, ...]] = {
    "source_scan_order_only": ("insert-query-index-order", "insert-query-index-order-keeps-other-rows"),
    "alternatives_dropped": ("insert-query-index-order",),
    "source_always_streams": ("insert-query-source-error-collected",),
    "source_always_collects": ("insert-query-source-error-keeps-no-row",),
    "returning_does_not_collect": ("insert-query-fail-collects-with-returning",),
    "transfer_rowids_ignored": ("insert-query-transfer-with-rowid-gap",),
    "transfer_takes_any_projection": ("insert-query-fail-streams-without-trigger",),
    "rules_with_two_orders": ("insert-query-trigger-two-orders",),
    "source_failure_has_no_output": ("insert-query-source-error-keeps-no-row",),
}
"""Native cases that distinguish each changed rule from the original model."""

BOUNDARIES: frozenset[str] = frozenset({"transfer_rowids_ignored", "rules_with_two_orders"})
"""The mutants whose target case is outside the model, so that the model must stay unsupported."""

GUARDS: dict[str, str] = {
    "source_scan_order_only": "rule:Table.accessOrders",
    "alternatives_dropped": "rule:insertSelectRun",
    "source_always_streams": "rule:insertSelectRun",
    "source_always_collects": "rule:insertSelectRun",
    "returning_does_not_collect": "rule:Resolved.Statement.collectsSource",
    "transfer_rowids_ignored": "rule:insertSelectTransferReady",
    "transfer_takes_any_projection": "rule:insertSelectTransferRowids",
    "rules_with_two_orders": "rule:insertSelectRun",
    "source_failure_has_no_output": "rule:statementOutput",
}
"""The model declarations whose meaning each mutant checks."""
