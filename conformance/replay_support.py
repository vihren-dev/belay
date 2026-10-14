"""Support for replaying many corpus cases quickly: the classifier in batches, and the
garbage collector paused while a corpus is decoded and replayed.

Profiling the frozen v5 progress test showed both costs: one classifier process for
each case of the query diagnostic, and the cyclic garbage collector walking millions of
decoded objects again on each full collection.
"""

from collections.abc import Iterator
from contextlib import contextmanager
import gc
from pathlib import Path

from conformance.case_format import Json
from conformance.model_check import compiled_many


@contextmanager
def collection_paused() -> Iterator[None]:
    """Pause Python's cyclic garbage collector, and restore its state afterwards.

    Decoded JSON has no reference cycles, so reference counting frees it without the
    collector. A corpus has millions of decoded objects, and each full collection walks
    all of them again: for corpus v5 the collector took 7 of the 11 seconds of `load`.
    """
    enabled = gc.isenabled()
    gc.disable()
    try:
        yield
    finally:
        if enabled:
            gc.enable()


RUNNER_BATCH = 256
"""Cases per run of the compiled classifier: each run costs a process start, and a
batch must finish within the runner's time limit (`model_check.compiled_many`)."""


def classify(cases: list[dict[str, Json]], runtime: Path) -> list[dict[str, Json]]:
    """Classify the cases in order with the compiled classifier, in batches of
    `RUNNER_BATCH`, so that many cases need few process starts."""
    return [answer for start in range(0, len(cases), RUNNER_BATCH)
            for answer in compiled_many(cases[start:start + RUNNER_BATCH], runtime)]
