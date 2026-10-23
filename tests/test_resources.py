"""Resource failures must happen before snapshots, toolchain installs or package copies."""

from pathlib import Path
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

import pytest

from tools.check_resources import (MAX_ENVIRONMENT_BYTES, MIN_FREE_BYTES, check_environment,
                                   check_resources, existing_parent)

pytestmark = [pytest.mark.unit, pytest.mark.environment]


def test_separate_temporary_filesystem() -> None:
    """Enough workspace capacity cannot hide a full temporary filesystem."""
    separate = MagicMock(spec=Path)
    separate.stat.return_value.st_dev = -1
    separate.__str__.return_value = '/separate/tmp'

    def destination(path: Path) -> Path:
        """Model a temporary volume independent of the real workspace."""
        return separate if path == Path('/separate/tmp') else existing_parent(path)

    def capacity(path: Path) -> SimpleNamespace:
        """Only the separate temporary destination lacks capacity."""
        return SimpleNamespace(free=0 if path is separate else MIN_FREE_BYTES)

    with patch('tools.check_resources.check_environment'), \
         patch('tools.check_resources.tempfile.gettempdir', return_value='/separate/tmp'), \
         patch('tools.check_resources.existing_parent', side_effect=destination), \
         patch('tools.check_resources.shutil.disk_usage', side_effect=capacity):
        with pytest.raises(ValueError, match='/separate/tmp: 0.00 GiB'):
            check_resources(Path.cwd())


def test_environment_and_capacity_boundaries(tmp_path: Path) -> None:
    """`check_environment` accepts the files of `ENVIRONMENT_FILES` and rejects oversized or
    symlinked inputs, and `check_resources` rejects low-space destinations."""
    environment = tmp_path / 'nix'
    environment.mkdir()
    flake = environment / 'flake.nix'
    flake.write_text('{}')
    (environment / 'flake.lock').write_text('{}')
    (environment / 'sqlite.nix').write_text('{}')
    (environment / 'dev-shell.nix').write_text('{}')
    assert check_environment(tmp_path) == 8
    with patch('tools.check_resources.shutil.disk_usage', return_value=SimpleNamespace(free=MIN_FREE_BYTES)):
        check_resources(tmp_path)
    with patch('tools.check_resources.shutil.disk_usage', return_value=SimpleNamespace(free=MIN_FREE_BYTES - 1)):
        with pytest.raises(ValueError, match='10 GiB'):
            check_resources(tmp_path)
    with flake.open('wb') as output:
        output.truncate(MAX_ENVIRONMENT_BYTES + 1)
    with pytest.raises(ValueError, match='exceed 1 MiB'):
        check_environment(tmp_path)
    flake.unlink()
    outside = tmp_path / 'outside.nix'
    outside.write_text('{}')
    flake.symlink_to(outside)
    with pytest.raises(ValueError, match='Unexpected environment input'):
        check_environment(tmp_path)
    flake.unlink()
    flake.write_text('{}')
    (environment / 'dist').mkdir()
    with pytest.raises(ValueError, match='Unexpected environment input'):
        check_environment(tmp_path)
