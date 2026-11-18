# Refute the consumer-size claim under CI load

Created 2026-11-18 for [issue #426](https://github.com/vihren-dev/belay/issues/426).

The consumer-size fixture must retain its full schema, its two counterexamples,
and the replay against pinned SQLite. The generated counterexample must use
the default sampling options, including at most two rows per table. Only this
fixture uses 60 seconds of compiled work per check. The product default
remains 10 seconds.

The owner approved the fixture limit on 2026-11-18. The regression in
`tests/surface_check_consumer_size_test.py` checks the schema size, both
counterexamples and the trigger's CHECK failure on replay.
