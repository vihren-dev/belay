"""Enable native reportlog for every repository session and finalize outside Nix builders."""

from collections.abc import Mapping
from datetime import datetime, timezone
import fcntl
import os
from typing import BinaryIO
from uuid import uuid4

import pytest

from tools.observability_provenance import provenance
from tools.observability_records import diagnostic, encode
from tools.observability_spool import attempt_upload, spool

PRODUCER = pytest.StashKey[BinaryIO]()
"""The producer owns this lock until reportlog has closed, including during test failures."""


def pytest_addoption(pluginmanager: pytest.PytestPluginManager) -> None:
    """Explicitly load the dependency even when Nix disables plugin autoloading."""
    pluginmanager.import_plugin("pytest_reportlog", consider_entry_points=True)


def host_metadata(environment: Mapping[str, str]) -> dict[str, str]:
    """The provenance of a session outside a Nix builder, so a query can separate local, pull
    request and main sessions. A builder writes nothing: the host Nix wrapper adds the values
    when it imports the execution, and a store output must not depend on them."""
    return {} if environment.get("BELAY_OBSERVABILITY_BUILD") == "1" else provenance(environment)


@pytest.hookimpl(tryfirst=True)
def pytest_configure(config: pytest.Config) -> None:
    """Assign a fresh execution directory before reportlog opens its output."""
    if hasattr(config, "workerinput"):
        return
    try:
        # Copied pytest harnesses inherit a persistent spool instead of losing reports with tmp_path.
        os.environ.setdefault("BELAY_OBSERVABILITY_SPOOL", str(spool().resolve()))
        identity = str(uuid4())
        directory = spool() / identity
        directory.mkdir(parents=True)
        handle = (directory / ".lock").open("ab")
        fcntl.flock(handle, fcntl.LOCK_EX)
        config.stash[PRODUCER] = handle
        (directory / "execution.json").write_text(encode({
            "execution_id": identity, "started_at": datetime.now(timezone.utc).isoformat(),
            "metadata": host_metadata(os.environ),
        }) + "\n")
        config.option.report_log = str(directory / "report.jsonl")
    except OSError as error:
        config.option.report_log = None
        diagnostic(f"cannot create report ({type(error).__name__}); test status is unchanged")


@pytest.hookimpl(trylast=True)
def pytest_unconfigure(config: pytest.Config) -> None:
    """Reportlog closes first; release the producer lock and retry all pending observations."""
    handle = config.stash.get(PRODUCER, None)
    if handle is not None:
        handle.close()
        attempt_upload()
