"""Run the existing Nix command, recover report artifacts and upload outside the builder."""

import argparse
from datetime import datetime, timezone
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from time import monotonic

from tests.runtime_support import CommandResult, CommandStreams
from tools.observability_logs import recover
from tools.observability_provenance import provenance
from tools.observability_records import diagnostic, encode, execution, json_object
from tools.observability_spool import attempt_upload, import_execution, spool

STORE = "/nix/store/"
"""Only store paths in the output of the Nix command are read as outputs."""
SUITE_OUTPUT = re.compile(r"[0-9a-z]{32}-sqlite-verifier-test-(.+)-1")
"""The store path name of a Nix test suite output (`build-support/tests.nix`), with the suite name."""


def build(arguments: list[str], timeout: int) -> CommandResult:
    """Keep the builder client in the enclosing CI process group and bound it with GNU timeout."""
    started = monotonic()
    with subprocess.Popen(["timeout", "--foreground", "--kill-after=5", str(timeout), *arguments],
                          stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE) as process:
        streams = CommandStreams(process, echo=True)
        closed = streams.read_until(started + timeout + 10)
        if not closed:
            process.kill()
        process.wait(timeout=5)
        stdout, stderr = streams.close()
    return CommandResult(tuple(arguments), process.returncode, stdout, stderr,
                         monotonic() - started, not closed or process.returncode == 124)


def import_with(source: Path, destination: Path, metadata: dict[str, str]) -> None:
    """Import a copy of the execution whose manifest adds `metadata`; the builder's files stay unchanged."""
    execution(source)
    with tempfile.TemporaryDirectory(prefix="belay-provenance-") as temporary:
        staged = Path(temporary) / source.name
        staged.mkdir()
        for name in ("execution.json", "report.jsonl"):
            if (source / name).is_symlink():
                raise ValueError("artifact files must not be symlinks")
        manifest = json_object((source / "execution.json").read_bytes())
        builder = manifest.get("metadata", {})
        manifest["metadata"] = {**(builder if isinstance(builder, dict) else {}), **metadata}
        (staged / "execution.json").write_text(encode(manifest) + "\n")
        shutil.copyfile(source / "report.jsonl", staged / "report.jsonl")
        import_execution(staged, destination)


def started_since(manifest: Path, since: datetime) -> bool:
    """Whether the builder of this execution ran during the command. A cached or substituted
    output started earlier; the command that built it imported it, and importing it again would
    replace its provenance in ClickHouse, which keeps the last row of an execution."""
    started = datetime.fromisoformat(str(execution(manifest.parent)["started_at"]))
    return started.replace(tzinfo=timezone.utc) >= since


def collect_outputs(output: str, destination: Path, since: datetime, metadata: dict[str, str]) -> None:
    """Import each execution that ran during the command from each successful output or link-farm
    child, with the provenance and the suite name, without copying runtime store closures."""
    for line in output.splitlines():
        root = Path(line.strip())
        if not line.startswith(STORE) or not root.is_dir():
            continue
        folders = [root, *(child for child in root.iterdir() if child.is_dir())]
        for folder in folders:
            suite = SUITE_OUTPUT.fullmatch(folder.resolve().name)
            for manifest in (folder / "observability").glob("*/execution.json"):
                if started_since(manifest, since):
                    import_with(manifest.parent, destination, {**metadata, **({"suite": suite[1]} if suite else {})})


def recover_logs(lines: list[str], destination: Path, metadata: dict[str, str]) -> None:
    """Recover the reports of failed builders from the log into a staging spool, then import them
    with the provenance. The log does not tie a frame to its derivation, so they have no suite."""
    with tempfile.TemporaryDirectory(prefix="belay-recovered-") as temporary:
        recover(lines, Path(temporary))
        for folder in Path(temporary).iterdir():
            if (folder / "execution.json").exists():
                import_with(folder, destination, metadata)


def run(arguments: list[str], timeout: int) -> int:
    """Keep the build status even when log extraction or delivery fails."""
    attempt_upload()
    since = datetime.now(timezone.utc)
    metadata = provenance(os.environ)
    result = build(arguments, timeout)
    try:
        collect_outputs(result.stdout, spool(), since, metadata)
        recover_logs((result.stdout + "\n" + result.stderr).splitlines(), spool(), metadata)
    except (OSError, ValueError, KeyError) as error:
        diagnostic(f"artifact recovery failed ({type(error).__name__}); inspect the retained build log")
    attempt_upload()
    return 124 if result.timed_out else result.returncode


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=int, required=True)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    sys.exit(run(args.command, args.timeout))
