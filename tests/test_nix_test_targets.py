"""Check the real Nix test targets: their commands, failed-test behavior and flake checks."""

import json
from pathlib import Path
import shutil
import shlex
from uuid import uuid4

import pytest

from tests.runtime_support import run_command

ROOT = Path(__file__).resolve().parents[1]
pytestmark = [pytest.mark.integration, pytest.mark.environment, pytest.mark.requires_nix]


def nix_string(path: Path) -> str:
    """`path` as a Nix string literal; JSON quoting matches Nix's, except that `${` must not interpolate."""
    return json.dumps(str(path)).replace("${", "\\${")


def import_file(name: str) -> str:
    """A Nix expression that imports `build-support/NAME` of this checkout, so the evaluation tests use the
    real build definitions and only the source tree is private."""
    return f'import (builtins.toPath {nix_string(ROOT / "build-support" / name)})'


PRELUDE = f'''let
      pkgs = {import_file("locked-nixpkgs.nix")} {{}};
      builds = {import_file("default.nix")} {{}};
    in'''
"""Binds `pkgs` and the real builds of this checkout for the expressions below."""


def expression(root: Path) -> str:
    """Reuse the actual test definitions with a private source tree and unchanged built dependencies."""
    return f'''{PRELUDE} {import_file("tests.nix")} {{
      inherit pkgs; inherit (builds) leanToolchain conformance modelPackage leanPackages surfacePackage textPackage;
      parserLibrary = builds.parserLibrary.testRoot;
      root = /. + {nix_string(root)};
    }}'''


def test_bounded_commands_keep_complete_suite_ownership() -> None:
    """The real Nix command runs every owned file with a per-test limit and full reporting; the
    suite limit is 1200 seconds, and 2700 for a mutant suite, which runs alone on its CI runner.
    Only mutant suites stop after a reported failure, preserving diagnostics before their deadline."""
    result = run_command(['nix-instantiate', '--eval', '--strict', '--json',
        '--extra-experimental-features', 'nix-command flakes', '--expr',
        f'builtins.mapAttrs (_: test: test.installPhase) ({expression(ROOT)})'], cwd=ROOT, timeout=30)
    assert result.returncode == 0, result.diagnostic()
    scripts = json.loads(result.stdout)
    ownership = json.loads((ROOT / 'tests/nix_suites.json').read_text())
    assert set(scripts) == set(ownership) == {'model', 'coverageStatements', 'coverageFeatures', 'frozen', 'corpora', 'harness', 'sample', 'upstream', 'parserLibrary', 'packages',
                                               'documentation', 'theoremDependencies', 'mutants', 'tableMutants', 'functionMutants', 'surface',
                                               'writers'}
    mutant_suites = set(json.loads((ROOT / 'tests/nix_mutant_suites.json').read_text()))
    for name, script in scripts.items():
        command = shlex.split(next(line for line in script.replace('\\\n', ' ').splitlines()
                                  if line.strip().startswith('timeout ')))
        limit = '2700' if name in mutant_suites else '1200'
        assert command[:5] == ['timeout', limit, 'python3', '-m', 'pytest'], (name, command[:5])
        runtime_index = command.index('--runtime-root')
        assert command[5:runtime_index] == ownership[name], (name, command)
        early_failure = ['--exitfirst'] if name in mutant_suites else []
        assert command[runtime_index + 2:] == ['-p', 'no:cacheprovider', '-p', 'pytest_timeout', '--timeout=300',
            *early_failure, '--junitxml', '$out/junit.xml', '-v', '--durations=10'], (name, command)


@pytest.fixture
def source_tree(tmp_path: Path) -> Path:
    """Copy only small potential test inputs; no store outputs, vendored parsers or build trees."""
    for name in ('pytest.ini', 'conftest.py', 'LICENSE'):
        shutil.copy2(ROOT / name, tmp_path / name)
    for name in ('tests', 'belay', 'conformance', 'docs', 'packages', 'reports', 'nix', 'build-support', 'tools'):
        shutil.copytree(ROOT / name, tmp_path / name,
                        ignore=shutil.ignore_patterns('__pycache__', '*.pyc', 'upstream'))
    return tmp_path


def test_failed_pytest_target_has_no_output(source_tree: Path) -> None:
    """A real sandboxed target with a failed pytest assertion cannot create a reusable successful output."""
    (source_tree / 'tests/parser_library_test.py').write_text('''import pytest
pytestmark = [pytest.mark.integration]
def test_failure():
    """Deliberate failure must propagate through the Nix build."""
    assert False, "intentional pytest failure"
''')
    result = run_command(['nix-build', '--no-out-link', '--option', 'sandbox', 'true',
        '--option', 'sandbox-fallback', 'false', '--extra-experimental-features', 'nix-command flakes',
        '--expr', f'({expression(source_tree)}).parserLibrary'], cwd=ROOT, timeout=90)
    assert result.returncode != 0, result.diagnostic()
    assert 'intentional pytest failure' in result.stderr, result.diagnostic()


@pytest.fixture(scope="session")
def flake_source(tmp_path_factory: pytest.TempPathFactory) -> Path:
    """Nix 2.18 needs a Git source boundary for a subdirectory flake, including in jj workspaces."""
    destination = tmp_path_factory.mktemp("flake-source") / "checkout"
    shutil.copytree(ROOT, destination, symlinks=True, ignore=shutil.ignore_patterns(
        ".git", ".jj", ".lake", ".direnv", ".pytest_cache", "build", "dist", "lean",
        "result*", "__pycache__", "*.pyc"))
    for command in (["git", "init", "-q"], ["git", "add", "."]):
        result = run_command(command, cwd=destination, timeout=30)
        assert result.returncode == 0, result.diagnostic()
    return destination


@pytest.mark.parametrize('system', ['aarch64-darwin', 'x86_64-linux'])
def test_flake_checks_reuse_existing_targets(system: str, flake_source: Path) -> None:
    """Flake checks expose the same derivations as the legacy entrypoint, preserving cached results."""
    flags = ['--extra-experimental-features', 'nix-command flakes']
    projection = 'builtins.mapAttrs (_: test: test.drvPath)'
    flake = run_command(['nix', *flags, 'eval', '--json', '--no-update-lock-file',
                         f'git+file://{flake_source}?dir=nix#checks.{system}', '--apply', projection], cwd=ROOT, timeout=60)
    legacy = run_command(['nix-instantiate', *flags, '--eval', '--strict', '--json', '--expr',
        f'{projection} ((import ./build-support/default.nix {{ system = "{system}"; }}).tests)'],
        cwd=ROOT, timeout=60)
    assert flake.returncode == 0, flake.diagnostic()
    assert legacy.returncode == 0, legacy.diagnostic()
    checks = json.loads(flake.stdout)
    scheduled = set(json.loads((ROOT / 'tests/nix_scheduled_suites.json').read_text()))
    assert set(checks) == set(json.loads((ROOT / 'tests/nix_suites.json').read_text())) - scheduled
    assert checks == json.loads(legacy.stdout)


def test_surface_manifest_evaluates_before_filtered_source_is_stored(tmp_path: Path) -> None:
    """Our dependency pin/mapping must evaluate read-only when the filtered surface is cold.
    A unique source nonce prevents a warm store from hiding a read of an unrealized source."""
    package = tmp_path / "packages/belay"
    package.mkdir(parents=True)
    for name in ("lake-manifest.json", "lean-toolchain"):
        shutil.copy2(ROOT / "packages/belay" / name, package / name)
    (package / "ColdProbe.lean").write_text(f"-- Cold evaluation source {uuid4()}\n")
    builds = f'({import_file("default.nix")} {{ root = /. + {nix_string(tmp_path)}; }})'
    command = ["nix-instantiate", "--eval", "--strict", "--json",
               "--extra-experimental-features", "nix-command flakes", "--expr"]
    source = run_command([*command, f"toString {builds}.sources.surface"], cwd=ROOT, timeout=30)
    assert source.returncode == 0, source.diagnostic()
    filtered = Path(json.loads(source.stdout))
    assert not filtered.exists(), f"cold probe unexpectedly materialized {filtered}"
    manifest = run_command([*command, f"{builds}.surfacePackage.postPatch"], cwd=ROOT, timeout=30)
    assert manifest.returncode == 0, manifest.diagnostic()
    script = json.loads(manifest.stdout)
    assert 'require plausible from ".lake/packages/plausible"' in script, script
    assert "surface-lake-manifest.json" in script, script
    assert not filtered.exists(), f"read-only manifest evaluation materialized {filtered}"
