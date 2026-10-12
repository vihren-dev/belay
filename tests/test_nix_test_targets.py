"""Check the real Nix test targets: their commands, failed-test behavior and flake checks."""

import json
from pathlib import Path
import shutil
import shlex

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


def runtime_expression(root: Path, sources: str) -> str:
    """The real runtime derivation (`runtime.nix`) built from the `sources` attribute of `sources.nix` for
    the source tree `root`; Nix only evaluates it, so the tests see its true inputs."""
    return f'''{import_file("runtime.nix")} {{
        inherit pkgs; inherit (builds) leanToolchain leanRuntime modelPackage sources verifierLibrary;
        parserLibrary = builds.parserLibrary.library;
        src = ({import_file("sources.nix")} {{ inherit (pkgs) lib; root = /. + {nix_string(root)}; }}).{sources};
      }}'''


PRELUDE = f'''let
      pkgs = {import_file("locked-nixpkgs.nix")} {{}};
      builds = {import_file("default.nix")} {{}};
    in'''
"""Binds `pkgs` and the real builds of this checkout for the expressions below."""


def expression(root: Path) -> str:
    """Reuse the actual test definitions with a private source tree and unchanged runtime dependencies."""
    return f'''{PRELUDE} {import_file("tests.nix")} {{
      inherit pkgs; inherit (builds) leanToolchain leanRuntime conformance modelPackage leanPackages;
      parserLibrary = builds.parserLibrary.testRoot;
      runtime = {runtime_expression(root, "runtime")};
      seedRuntime = {runtime_expression(root, "runtimeWithoutExamples")};
      root = /. + {nix_string(root)};
    }}'''


def test_bounded_commands_keep_complete_suite_ownership() -> None:
    """The real Nix command runs every owned file with a per-test limit and full reporting."""
    result = run_command(['nix-instantiate', '--eval', '--strict', '--json',
        '--extra-experimental-features', 'nix-command flakes', '--expr',
        f'builtins.mapAttrs (_: test: test.installPhase) ({expression(ROOT)})'], cwd=ROOT, timeout=30)
    assert result.returncode == 0, result.diagnostic()
    scripts = json.loads(result.stdout)
    ownership = json.loads((ROOT / 'tests/nix_suites.json').read_text())
    assert set(scripts) == set(ownership) == {'atuin', 'bundle', 'cli', 'kernel', 'model', 'frozen', 'corpora',
                                               'harness', 'sample', 'upstream', 'parserLibrary', 'packages',
                                               'documentation'}
    for name, script in scripts.items():
        command = shlex.split(next(line for line in script.replace('\\\n', ' ').splitlines()
                                  if line.strip().startswith('timeout ')))
        assert command[:5] == ['timeout', '1200', 'python3', '-m', 'pytest']
        runtime_index = command.index('--runtime-root')
        assert command[5:runtime_index] == ownership[name], (name, command)
        assert command[runtime_index + 2:] == ['-p', 'no:cacheprovider', '-p', 'pytest_timeout', '--timeout=300',
            '--junitxml', '$out/junit.xml', '-v', '--durations=10'], (name, command)


@pytest.fixture
def source_tree(tmp_path: Path) -> Path:
    """Copy only small potential test inputs; no store outputs, vendored parsers or build trees."""
    for name in ('pytest.ini', 'conftest.py', 'LICENSE'):
        shutil.copy2(ROOT / name, tmp_path / name)
    for name in ('tests', 'migration_check', 'belay', 'conformance', 'examples', 'docs', 'packaging', 'packages', 'reports', 'nix', 'build-support', 'tools'):
        shutil.copytree(ROOT / name, tmp_path / name,
                        ignore=shutil.ignore_patterns('__pycache__', '*.pyc', 'upstream'))
    for name in ("cases.py", "stage_timing.py"):
        path = tmp_path / "experiments/adr-0003-latency" / name
        path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / "experiments/adr-0003-latency" / name, path)
    return tmp_path


def test_failed_pytest_target_has_no_output(source_tree: Path) -> None:
    """A real sandboxed target with a failed pytest assertion cannot create a reusable successful output."""
    (source_tree / 'tests/kernel_gate_test.py').write_text('''import pytest
pytestmark = [pytest.mark.integration, pytest.mark.kernel]
def test_failure():
    """Deliberate failure must propagate through the Nix build."""
    assert False, "intentional pytest failure"
''')
    result = run_command(['nix-build', '--no-out-link', '--option', 'sandbox', 'true',
        '--option', 'sandbox-fallback', 'false', '--extra-experimental-features', 'nix-command flakes',
        '--expr', f'({expression(source_tree)}).kernel'], cwd=ROOT, timeout=90)
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
    assert set(checks) == set(json.loads((ROOT / 'tests/nix_suites.json').read_text()))
    assert checks == json.loads(legacy.stdout)


def target_derivations(root: Path) -> dict[str, str]:
    """The derivation path of each Nix test target for a source tree.

    Two evaluations that differ only in one source file show which targets that file
    invalidates, without building anything.
    """
    result = run_command(['nix-instantiate', '--eval', '--strict', '--json',
        '--extra-experimental-features', 'nix-command flakes', '--expr',
        f'builtins.mapAttrs (_: test: test.drvPath) ({expression(root)})'], cwd=ROOT, timeout=120)
    assert result.returncode == 0, result.diagnostic()
    return json.loads(result.stdout)


def test_case_reader_change_reruns_only_targets_that_use_it(source_tree: Path) -> None:
    """`build-support/tests.nix` gives the belay.toml reader only to the targets whose tests read cases, so
    changing it does not rerun the conformance, kernel or parser targets (ADR 0010 section 11)."""
    shutil.copytree(ROOT / 'judge', source_tree / 'judge')  # an input of the corpora target
    before = target_derivations(source_tree)
    reader = source_tree / 'migration_check/project_config.py'
    reader.write_text(reader.read_text() + '\n# A changed reader.\n')
    after = target_derivations(source_tree)
    assert {name for name in before if before[name] != after[name]} == {'atuin', 'bundle', 'cli'}


def seed_derivations(root: Path) -> dict[str, str]:
    """The derivation path of each case seed (`build-support/case-seeds.nix`) for a source tree, built with
    the same runtime as `default.nix` gives the seeds."""
    expression = (f'{PRELUDE} builtins.mapAttrs (_: seed: seed.drvPath) ({import_file("case-seeds.nix")} {{ '
                  f'inherit pkgs; runtime = {runtime_expression(root, "runtimeWithoutExamples")}; '
                  f'root = /. + {nix_string(root)}; }})')
    result = run_command(['nix-instantiate', '--eval', '--strict', '--json',
        '--extra-experimental-features', 'nix-command flakes', '--expr', expression], cwd=ROOT, timeout=120)
    assert result.returncode == 0, result.diagnostic()
    return json.loads(result.stdout)


def test_every_case_folder_has_one_seed(source_tree: Path) -> None:
    """`case-seeds.nix` finds the cases from their folders: one seed for each folder with a `belay.toml`."""
    folders = {path.parent.relative_to(source_tree).as_posix()
               for path in (source_tree / 'examples').rglob('belay.toml')}
    assert folders and set(seed_derivations(source_tree)) == folders


def test_case_change_rebuilds_only_its_seed(source_tree: Path) -> None:
    """A seed's inputs are what its `belay.toml` names and a runtime without examples/, so editing one
    case's proof changes only that case's seed (ADR 0010 section 8)."""
    before = seed_derivations(source_tree)
    proof = source_tree / 'examples/table_then_column/Proofs.lean'
    proof.write_text(proof.read_text() + '\n-- A changed proof.\n')
    after = seed_derivations(source_tree)
    assert {name for name in before if before[name] != after[name]} == {'examples/table_then_column'}
