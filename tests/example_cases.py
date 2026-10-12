"""Shipped example cases that the exporter, bundle and model-roots tests prepare, and their input digests."""

import hashlib
import json
from pathlib import Path

from migration_check.project_config import load

CASES = {"small": "add_column_then_table", "refutation": "missing_required_column", "atuin": "atuin"}
"""Current shipped positive, refutation and Atuin cases, by their names in recorded results."""


TOOL_OWNED = frozenset({"Generated", ".lake", ".belay"})
"""Folders of a proofs project that `prepare` and Lake write; they are outputs, not inputs."""


def list_candidate_module(project: Path, module: str) -> None:
    """Add a helper module to the roots of the proofs project's `Candidate` library, as its author would;
    `prepare` refuses a module that no library lists."""
    lakefile = project / "lakefile.toml"
    marker = 'name = "Candidate"\nsrcDir = "."\nroots = ['
    text = lakefile.read_text()
    assert marker in text, lakefile
    lakefile.write_text(text.replace(marker, marker + json.dumps(module) + ", ", 1))


def case_inputs(examples: Path, folder: str) -> tuple[str, str, str, str, str]:
    """Contract, candidate and schema paths relative to `examples`, profile and expected status of one case.

    They come from the case's `belay.toml`, so the test runs the case that users see.
    """
    config = load(examples / folder / "belay.toml", examples)
    assert config.test_status is not None, config.file
    root = examples.resolve()
    return (config.contract.relative_to(root).as_posix(), config.proofs.relative_to(root).as_posix(),
            config.schema.relative_to(root).as_posix(), config.profile, config.test_status)


def file_digest(path: Path) -> str:
    """Bind the actual bytes consumed by the current native acceptance check."""
    return hashlib.sha256(path.read_bytes()).hexdigest()


def input_digests(examples: Path, approved: str, candidate: str, schema: str) -> dict[str, str]:
    """Bind SQL and all local Lean sources available to the selected contract and candidate."""
    files = {examples / schema, examples / candidate / "migration.sql"}
    for directory in (examples / approved, examples / candidate):
        files.update(path for path in directory.rglob("*.lean")
                     if not TOOL_OWNED.intersection(path.relative_to(directory).parts))
    return {path.relative_to(examples).as_posix(): file_digest(path) for path in sorted(files)}
