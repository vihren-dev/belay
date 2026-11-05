"""Recover CI observations as data using trusted code; replay retained artifacts before expiry."""

import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import tempfile
from time import monotonic
from uuid import UUID
import zipfile

from tools.observability_records import diagnostic
from tools.observability_logs import FILES
from tools.observability_spool import attempt_upload, import_execution, spool

ARTIFACT_PREFIX = "belay-observability-"
"""Only artifacts explicitly published for telemetry are read by the trusted upload job."""
MAX_BYTES = 256 * 1024 * 1024
"""Bound both archive and expanded data from untrusted test jobs."""
RECOVERY_SECONDS = 18 * 60
"""Leave two minutes for listing and shutdown inside the 20-minute CI job."""
API_SECONDS = 60
"""Bound each GitHub listing or download command independently."""


def import_archive(archive: Path, destination: Path) -> None:
    """Read only regular manifest/report files; never extract paths or execute artifact content."""
    if archive.stat().st_size > MAX_BYTES:
        raise ValueError("archive exceeds 256 MiB")
    with tempfile.TemporaryDirectory(prefix="belay-ci-") as temporary, zipfile.ZipFile(archive) as zipped:
        root = Path(temporary)
        total = 0
        for member in zipped.infolist():
            path = PurePosixPath(member.filename)
            if path.name not in FILES:
                continue
            if path.is_absolute() or ".." in path.parts or len(path.parts) < 2:
                raise ValueError("invalid artifact path")
            if stat.S_ISLNK(member.external_attr >> 16):
                raise ValueError("artifact contains a symlink")
            identity = str(UUID(path.parent.name))
            total += member.file_size
            if total > MAX_BYTES:
                raise ValueError("expanded artifact exceeds 256 MiB")
            folder = root / identity
            folder.mkdir(exist_ok=True)
            target = folder / path.name
            if target.exists():
                raise ValueError("duplicate artifact member")
            target.write_bytes(zipped.read(member))
        for folder in root.iterdir():
            import_execution(folder, destination)


def main() -> None:
    """Use read-only GitHub access and trusted environment configuration, never a PR checkout."""
    repository = os.environ["GITHUB_REPOSITORY"]
    if not re.fullmatch(r"[\w.-]+/[\w.-]+", repository):
        raise ValueError("invalid GITHUB_REPOSITORY")
    run_id = os.environ.get("BELAY_OBSERVABILITY_RUN_ID", "")
    if run_id and not run_id.isdecimal():
        raise ValueError("invalid workflow run ID")
    suffix = f"runs/{run_id}/artifacts" if run_id else "artifacts"
    result = subprocess.run(["gh", "api", "--paginate", f"repos/{repository}/actions/{suffix}?per_page=100",
                             "--jq", '.artifacts[] | {id,name,expired,created_at,size_in_bytes}'],
                            capture_output=True, text=True, check=True, timeout=API_SECONDS)
    artifacts = [json.loads(line) for line in result.stdout.splitlines()]
    deadline = monotonic() + RECOVERY_SECONDS
    for artifact in sorted(artifacts, key=lambda item: item["created_at"]):
        if monotonic() >= deadline:
            diagnostic("CI replay deadline reached; remaining artifacts await the next scheduled run")
            break
        if (artifact["expired"] or not artifact["name"].startswith(ARTIFACT_PREFIX)
                or artifact["size_in_bytes"] > MAX_BYTES):
            continue
        identity = artifact["id"]
        if not isinstance(identity, int) or identity <= 0:
            raise ValueError("invalid artifact ID")
        try:
            with tempfile.TemporaryDirectory(prefix="belay-download-") as temporary:
                archive = Path(temporary) / "reports.zip"
                with archive.open("wb") as output:
                    subprocess.run(["gh", "api", f"repos/{repository}/actions/artifacts/{identity}/zip"],
                                   stdout=output, check=True, timeout=API_SECONDS)
                import_archive(archive, spool())
                attempt_upload()
        except (OSError, ValueError, subprocess.SubprocessError, zipfile.BadZipFile) as error:
            diagnostic(f"artifact {identity}: recovery failed ({type(error).__name__}); retained on GitHub")


if __name__ == "__main__":
    main()
