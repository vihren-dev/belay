"""Recorded native observations that the record replay cannot compare, and why (ADR 0019)."""

HIDDEN_ROWID_REASON = "column names rowid, _rowid_ and oid are not modeled; rename the column"
"""The reason of a case whose table hides its rowid, as the model's restriction of these names says."""

OBSERVED_VIEW_REASON = ("the record replay compares tables only; a record with a view is judged through its predictions "
                        "(`conformance.predict`)")
"""The reason of a replayed case whose native observation lists a view."""


class ObservedView(ValueError):
    """A recorded observation that lists a view. The replay comparison has no view type: the
    model's view rows are observations, which the prediction path compares."""


class HiddenRowid(ValueError):
    """A recorded table whose columns take every rowid name, so SQLite's rowid has none and the
    recorder keys the rows by all columns; the model refuses the names, so the case is out of scope."""
