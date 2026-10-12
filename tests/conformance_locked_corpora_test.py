"""Complete validation of the corpora that the judge lock protects (`conformance.locked_corpora`).

`conformance.corpus.load` only decodes a locked corpus. This test is where each locked corpus
gets the complete validation by the current validator, so it finds an honest mistake in a
corpus or in the validator. It forms the `corpora` Nix suite, which runs again only when a
corpus or a module that the validation imports changes, such as in the pull request that
changes the judge lock (ADR 0011).
"""

import gzip
import json
from pathlib import Path
import shutil

import pytest

from conformance.corpus import load, validated_load
from conformance.locked_corpora import ROOT, is_locked, locked_directories, locked_file_records
from conformance.native_storage import serialized

SMALL = "conformance/synthetic-workload/corpus"
pytestmark = [pytest.mark.integration, pytest.mark.conformance]
LOCKED = sorted(path.relative_to(ROOT).as_posix() for path in locked_directories())
"""The claimed corpora, relative to the repository root."""


@pytest.mark.parametrize("label", LOCKED)
def test_locked_corpus_passes_complete_validation(label: str) -> None:
    """`validated_load` accepts each locked corpus, and `locked_file_records` decodes it equally.

    For a sharded corpus, the test compares one shard at a time, so only one shard of decoded
    records is in memory with the validated records. `decoded_record` copies each stored
    snapshot in its stored key order and `expanded_record` in sorted key order; the two agree
    when each stored line is canonical JSON, which the test also checks.
    """
    directory = ROOT / label
    assert is_locked(directory)
    manifest, validated = validated_load(directory)
    if "shards" not in manifest:
        assert not any("snapshots" in record for record in validated)
        return
    offset = 0
    for shard in manifest["shards"]:
        decoded = locked_file_records(directory, shard["path"])
        assert decoded == validated[offset:offset + len(decoded)], f"{label}/{shard['path']} decodes differently"
        offset += len(decoded)
        for line in gzip.decompress((directory / shard["path"]).read_bytes()).splitlines():
            assert serialized(json.loads(line)) == line, f"{label}/{shard['path']} has a non-canonical line"
    assert offset == len(validated)


def test_a_copy_gets_complete_validation_and_a_changed_copy_is_refused(tmp_path: Path) -> None:
    """`conformance.corpus.load`: only a claimed path is locked, so a copy is validated, and a
    changed shard in it gives the validator's error."""
    directory = Path(shutil.copytree(ROOT / SMALL, tmp_path / "corpus"))
    assert not is_locked(directory)
    assert load(directory) == validated_load(ROOT / SMALL)
    shard = next((directory / "shards").iterdir())
    payload = gzip.decompress(shard.read_bytes())
    shard.write_bytes(gzip.compress(payload.replace(b'"name":"', b'"name":"x', 1), mtime=0))
    with pytest.raises(ValueError, match="Corpus shard digest mismatch"):
        load(directory)
