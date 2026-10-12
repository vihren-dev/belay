"""Where Lake's artifact cache lives for `prepare` and `verify-bundle` (ADR 0010 section 4).

A cache belongs to one trust domain: every process that can write to it can put
outputs into it that later builds use without compiling. The caller chooses the
location and protects it like the installation and the approved sources. The
default is per user and named after the product, with one subfolder for each
runtime identity, because each Lean release makes the entries of the previous
one useless; `clean_other_versions` removes those folders.
"""

from collections.abc import Mapping
import hashlib
from pathlib import Path
import shutil

ENVIRONMENT_VARIABLE = "BELAY_CACHE_DIR"
"""Environment variable that names the cache folder, for CI and test fixtures."""

PRODUCT_FOLDER = "belay"
"""Folder name under the user's cache directory; it follows the product, not the command name."""


def runtime_version(sysroot: Path, libraries: tuple[Path, ...]) -> str:
    """A short identity of the toolchain and library build; a new build gets a new cache subfolder."""
    identity = "\n".join(str(path.resolve()) for path in (sysroot, *libraries))
    return hashlib.sha256(identity.encode()).hexdigest()[:16]


def default_root(environment: Mapping[str, str], home: Path, platform: str) -> Path:
    """The per-user cache root: `~/Library/Caches/belay` on macOS, else `$XDG_CACHE_HOME/belay`."""
    if platform == "darwin":
        return home / "Library/Caches" / PRODUCT_FOLDER
    base = environment.get("XDG_CACHE_HOME")
    return (Path(base) if base else home / ".cache") / PRODUCT_FOLDER


def cache_directory(option: Path | None, environment: Mapping[str, str], home: Path, platform: str,
                    version: str) -> Path:
    """The cache folder: `--cache DIR`, else `BELAY_CACHE_DIR`, else the version subfolder of the default root.

    An explicit folder is used as given, so a caller who names one also decides
    when it is cleaned.
    """
    if option is not None:
        return option.resolve()
    if environment.get(ENVIRONMENT_VARIABLE):
        return Path(environment[ENVIRONMENT_VARIABLE]).resolve()
    return default_root(environment, home, platform) / version


def clean_other_versions(root: Path, version: str) -> list[Path]:
    """Remove the subfolders of `root` that belong to other runtime versions; return what was removed."""
    removed = []
    if root.is_dir():
        for entry in sorted(root.iterdir()):
            if entry.is_dir() and not entry.is_symlink() and entry.name != version:
                shutil.rmtree(entry)
                removed.append(entry)
    return removed
