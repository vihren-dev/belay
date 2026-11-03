"""A change of the parser's C changes exactly the Nix packages that compile it (ADR 0023)."""

import json
from pathlib import Path
import shutil

import pytest

from tests.runtime_support import run_command
from tests.test_source_identity import IGNORED, ROOT

pytestmark = [pytest.mark.integration, pytest.mark.environment, pytest.mark.requires_nix]


def test_parser_change_rebuilds_only_the_packages_that_compile_it(tmp_path: Path) -> None:
    """A change under `parser/generated` changes the derivations of `textPackage` and `surfacePackage`
    of `build-support/default.nix`, which compile the parser with Lake, and not `modelPackage`."""
    root = tmp_path / "repository"
    shutil.copytree(ROOT, root, ignore=shutil.ignore_patterns(*IGNORED, "reviews"), symlinks=True)

    def drv_paths() -> dict[str, str]:
        """The derivation paths of the three packages for the copy of the repository."""
        names = ("modelPackage", "textPackage", "surfacePackage")
        body = " ".join(f"{name} = (set.{name}).drvPath;" for name in names)
        expression = (f"let set = import {json.dumps(str(root / 'build-support/default.nix'))} "
                      f"{{ root = /. + {json.dumps(str(root))}; }}; in {{ {body} }}")
        result = run_command(["nix", "eval", "--offline", "--impure", "--json", "--extra-experimental-features",
                              "nix-command flakes", "--expr", expression], cwd=ROOT, timeout=120)
        if result.returncode:
            raise ValueError(result.diagnostic())
        return json.loads(result.stdout)

    before = drv_paths()
    target = next((root / "parser/generated").glob("*/token_names.inc"))
    target.write_text(target.read_text() + "\n")
    after = drv_paths()
    assert {name for name in before if before[name] != after[name]} == {"textPackage", "surfacePackage"}
