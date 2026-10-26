"""The manifest digest of the definition modules of an authored corpus (ADR 0012 corpus writers)."""

import hashlib
from pathlib import Path

import pytest

from conformance.authored_evidence import AuthoredCorpus, definitions_digest

pytestmark = pytest.mark.unit


def corpus(definitions: Path, *more: Path) -> AuthoredCorpus:
    """A corpus that names only the definition modules; the digest reads nothing else."""
    return AuthoredCorpus(records=list, definitions=definitions, source_name="s", part="p", corpus_version=1,
                          evidence_kind="k", more_definitions=more)


def test_one_module_keeps_the_digest_of_its_bytes(tmp_path: Path) -> None:
    """A corpus of one module hashes exactly that module, so published manifests stay valid."""
    first = tmp_path / "first.py"
    first.write_bytes(b"first")
    assert definitions_digest(corpus(first)) == hashlib.sha256(b"first").hexdigest()


def test_each_further_module_changes_the_digest(tmp_path: Path) -> None:
    """The digest covers the further modules in order: editing any of them, or swapping two, changes it."""
    first, second = tmp_path / "first.py", tmp_path / "second.py"
    first.write_bytes(b"first")
    second.write_bytes(b"second")
    joined = definitions_digest(corpus(first, second))
    assert joined == hashlib.sha256(b"firstsecond").hexdigest() != definitions_digest(corpus(first))
    assert definitions_digest(corpus(second, first)) != joined
    second.write_bytes(b"second, edited")
    assert definitions_digest(corpus(first, second)) != joined
