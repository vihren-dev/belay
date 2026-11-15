"""The configuration of the top-level package `belay` (`lakefile.toml` and `lake-manifest.json` in the top-level
folder), which Reservoir reads: the package data, the version tags, and the pins of the packages that the root
inherits from the surface package in `packages/belay`."""

import json
from pathlib import Path
import shutil
import subprocess

import pytest

from tests.runtime_support import run_command

ROOT = Path(__file__).resolve().parents[1]
TAGS = ("v0.1.0", "v0.1.0-rc.1", "v0.1.1", "v0.1.2", "v0.2.0", "v1.0.0")
"""The four tags of the removed verifier product and two tags of this package."""


@pytest.mark.integration
@pytest.mark.requires_lean("compiler")
@pytest.mark.requires_native("git")
@pytest.mark.timeout(60)
def test_reservoir_reads_the_package_data_and_the_version_tags(lean_sysroot: Path, tmp_path: Path) -> None:
    """The fields `version`, `license`, `description`, `keywords` and `versionTags` of the root `lakefile.toml`:
    `lake reservoir-config` in a git repository with the root lakefile, a README and the tags of `TAGS` reports
    the name `belay`, the version 0.2.0, the license MIT, the README and only the tags v0.2.0 and v1.0.0. The
    tags v0.1.* are releases of the removed verifier product and are not versions of this package."""
    repository = tmp_path / "repository"
    repository.mkdir()
    shutil.copy(ROOT / "lakefile.toml", repository / "lakefile.toml")
    (repository / "README.md").write_text("A package.\n")
    git = ["git", "-c", "user.name=Test", "-c", "user.email=test@example.com", "-c", "commit.gpgsign=false"]
    for arguments in (["init", "-q"], ["add", "."], ["commit", "-q", "-m", "package"], *(["tag", tag] for tag in TAGS)):
        subprocess.run([*git, *arguments], cwd=repository, check=True, timeout=10, capture_output=True)
    result = run_command([str(lean_sysroot / "bin/lake"), "reservoir-config"], cwd=repository, timeout=40)
    assert result.returncode == 0, result.diagnostic()
    data = json.loads(result.stdout)
    assert {key: data[key] for key in ("name", "version", "license", "readmeFile", "versionTags")} == {
        "name": "belay", "version": "0.2.0", "license": "MIT", "readmeFile": "README.md",
        "versionTags": ["v0.2.0", "v1.0.0"]}, data
    assert data["description"] and data["keywords"], data


@pytest.mark.unit
def test_the_root_manifest_pins_the_packages_of_the_surface_manifest() -> None:
    """`lake-manifest.json` of the top-level folder: it requires the surface `belaySurface` by the path
    `packages/belay`, and it pins each package of the surface's manifest with the same source. Lake takes the pins
    of a project that requires the root from the root manifest, so a pin that differs from the surface's gives
    users other dependencies than the surface's own build."""
    root = json.loads((ROOT / "lake-manifest.json").read_text())
    surface = json.loads((ROOT / "packages/belay/lake-manifest.json").read_text())
    assert root["name"] == "belay" and surface["name"] == "belaySurface"
    pins = {entry["name"]: entry for entry in root["packages"]}
    assert {key: pins["belaySurface"][key] for key in ("type", "dir", "inherited")} == {
        "type": "path", "dir": "packages/belay", "inherited": False}
    assert set(pins) == {"belaySurface"} | {entry["name"] for entry in surface["packages"]}
    for entry in surface["packages"]:
        pin = pins[entry["name"]]
        assert pin["inherited"] and pin["type"] == entry["type"], (pin, entry)
        if entry["type"] == "git":
            assert (pin["url"], pin["rev"]) == (entry["url"], entry["rev"]), (pin, entry)
        else:
            assert Path("packages/belay", entry["dir"]) == Path(pin["dir"]), (pin, entry)
