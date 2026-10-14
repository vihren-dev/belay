"""`conformance.replay_support`: the garbage collector pause and the batched classifier.

The corpus replay relies on both to keep the frozen progress tests within their time
limit. These tests check that the pause restores the collector's state, also after an
error, and that batching keeps the order of answers across a batch boundary.
"""

import gc
from pathlib import Path

import pytest

from conformance import replay_support
from conformance.case_format import Json

pytestmark = [pytest.mark.unit]


@pytest.mark.parametrize("enabled", [True, False])
def test_collection_paused_restores_the_collector(enabled: bool) -> None:
    """The collector is off inside the block and back in its earlier state after it, also after an error."""
    was_enabled = gc.isenabled()
    try:
        (gc.enable if enabled else gc.disable)()
        with replay_support.collection_paused():
            assert not gc.isenabled()
        assert gc.isenabled() == enabled
        with pytest.raises(RuntimeError), replay_support.collection_paused():
            raise RuntimeError("stop")
        assert gc.isenabled() == enabled
    finally:
        (gc.enable if was_enabled else gc.disable)()


def test_classify_keeps_order_across_batches(monkeypatch: pytest.MonkeyPatch) -> None:
    """Cases go to the classifier in batches of `RUNNER_BATCH`, and the answers keep the order of the cases."""
    batches: list[int] = []

    def fake(cases: list[dict[str, Json]], runtime: Path) -> list[dict[str, Json]]:
        batches.append(len(cases))
        return [{"verdict": "AGREE", "index": case["index"]} for case in cases]

    monkeypatch.setattr(replay_support, "compiled_many", fake)
    cases: list[dict[str, Json]] = [{"index": index} for index in range(replay_support.RUNNER_BATCH + 3)]
    answers = replay_support.classify(cases, Path("runtime"))
    assert batches == [replay_support.RUNNER_BATCH, 3]
    assert [answer["index"] for answer in answers] == list(range(replay_support.RUNNER_BATCH + 3))
    batches.clear()
    assert replay_support.classify([], Path("runtime")) == [] and batches == []
