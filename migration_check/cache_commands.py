"""`clean-cache`: remove the default cache's folders of other verifier builds (ADR 0010, "Decisions")."""

import os
from pathlib import Path
import sys

from .cache_location import clean_other_versions, default_root, runtime_version
from .runtime import Runtime


def clean_cache() -> dict[str, object]:
    """Keep the current build's subfolder of the per-user default cache; remove the others."""
    runtime = Runtime.locate()
    root = default_root(os.environ, Path.home(), sys.platform)
    removed = clean_other_versions(root, runtime_version(runtime.sysroot, runtime.libraries))
    return {"status": "CLEANED", "root": str(root), "removed": [str(path) for path in removed]}
