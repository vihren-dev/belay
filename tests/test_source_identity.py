"""Real Nix fileset identities include each declared input and ignore generated trees.

The `parser` component holds the C that Lake compiles into the text package (ADR 0023): the
committed generated C, the C library headers, the library's files and each release's sqlite3.c."""

import json
from pathlib import Path
import shutil

import pytest

from tests.runtime_support import run_command

ROOT = Path(__file__).resolve().parents[1]
pytestmark = [pytest.mark.integration, pytest.mark.environment, pytest.mark.requires_nix]
PACKAGES: dict[str, str] = {"verifier-conformance": "verifierConformance", "public-doc-tools": "docTools"}
"""The Lean package folders under packages/ that `sources.nix` selects one by one, to their attributes."""
COMPONENTS: set[str] = {"model", "surface", "text", "parser", *PACKAGES.values()}
DYNAMIC: dict[str, set[str]] = {
    "packages/belay-sqlite-model/Belay/Sqlite/Model/Shared/Catalog/Database.lean": {"model"},
    "packages/belay-sqlite-model/Belay/Sqlite/Model/Frontend/Codecs/Codec.lean": {"model"},
    "packages/belay/Belay.lean": {"surface"}, "packages/belay/lakefile.lean": {"surface"},
    "packages/belay-sqlite-text/Belay/Sqlite/Frontend/Grammar/Parse.lean": {"text"},
    "packages/belay-sqlite-text/lakefile.lean": {"text"},
    **{f"parser/input.{suffix}": set() for suffix in ("py", "c", "h", "y", "json")},
    "parser/generated/parsers/0123456789abcdef/syntax.c": {"parser"},
    "parser/generated/tokenizers/0123456789abcdef/sqlite3_tokenizer.c": {"parser"}, "parser/generated/library_metadata.inc": {"parser"},
    "parser/generated/manifest.json": {"parser"},
    "parser/c-headers/string.h": {"parser"}, "parser/c-headers/stdio.h": {"parser"},
    "packages/verifier-conformance/VerifierConformance/Programs/Scripts/Trace.lean": {"verifierConformance"},
    "packages/verifier-conformance/ConformanceRunner.lean": {"verifierConformance"},
    "packages/public-doc-tools/PublicDocSyntax.lean": {"docTools"},
    "belay/sqlite/sql_model.py": set(), "tests/test_input.py": set(),
    "tools/helper.py": set(), "Loose.lean": set(), "conformance/check.py": set(),
}
FIXED: dict[str, set[str]] = {
    **{f"packages/belay-sqlite-model/{name}": {"model"}
       for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain")},
    **{f"packages/belay/{name}": {"surface"} for name in ("lake-manifest.json", "lean-toolchain")},
    **{f"packages/belay-sqlite-text/{name}": {"text"} for name in ("lake-manifest.json", "lean-toolchain", "c/parser_shim.c")},
    **{f"parser/{name}": {"parser"} for name in (
        "library.c", "library.h", "runtime.h", "tokenizer.c", "library_prefix.h", "library_tokenizer.c",
        "library_parser.c", "library_grammar.c")},
    **{f"packages/{folder}/{name}": {attribute} for folder, attribute in PACKAGES.items()
       for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain")},
}
PARENTS: tuple[str, ...] = (".", "parser", "belay/sqlite", "tests", "tools",
           "conformance", "packages/belay-sqlite-model", "packages/belay-sqlite-model/Belay/Sqlite/Model",
           "packages/belay", "packages/belay-sqlite-text", "packages/belay-sqlite-text/Belay/Sqlite",
           *(f"packages/{folder}" for folder in PACKAGES),
           "packages/verifier-conformance/VerifierConformance")
IGNORED: tuple[str, ...] = (".git", ".jj", ".lake", "build", "dist", "__pycache__")
def identities(root: Path) -> dict[str, str]:
    """Evaluate the checked-in fileset expression with the real locked package library, never build."""
    def literal(path: Path) -> str:
        """Quote paths as Nix strings, preserving spaces without permitting interpolation."""
        return json.dumps(str(path), ensure_ascii=False).replace("${", "\\${")
    expression = f'''let pkgs = import (builtins.toPath {literal(ROOT / 'build-support/locked-nixpkgs.nix')}) {{}};
      sources = import (builtins.toPath {literal(ROOT / 'build-support/sources.nix')}) {{ inherit (pkgs) lib;
      root = /. + {literal(root)}; }};
      in builtins.mapAttrs (_: source: toString source) sources'''
    result = run_command(["nix", "eval", "--offline", "--impure", "--json",
                          "--extra-experimental-features", "nix-command flakes", "--expr", expression],
                         cwd=ROOT, timeout=30)
    if result.returncode:
        raise ValueError(result.diagnostic())
    value = json.loads(result.stdout)
    assert set(value) == COMPONENTS and all(isinstance(path, str) for path in value.values()), value
    return value


@pytest.fixture(scope="session")
def identity_baseline(tmp_path_factory: pytest.TempPathFactory) -> tuple[Path, dict[str, str]]:
    """Build one tiny synthetic immutable baseline; no checkout, parser archives or build trees are copied."""
    root = tmp_path_factory.mktemp("source-identities")
    for name in (*DYNAMIC, *FIXED):
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"declared input {name}\n")
    return root, identities(root)


@pytest.fixture
def identity_tree(identity_baseline: tuple[Path, dict[str, str]], tmp_path: Path) -> tuple[Path, dict[str, str]]:
    """Every selected mutation receives private original bytes and the same unmodified baseline identity."""
    source, baseline = identity_baseline
    root = tmp_path / "source"
    shutil.copytree(source, root)
    return root, baseline


@pytest.mark.parametrize("relative", DYNAMIC)
def test_selected_membership(identity_tree: tuple[Path, dict[str, str]], relative: str) -> None:
    """Adding, editing, renaming and deleting this selected input changes exactly its declared components."""
    root, baseline = identity_tree
    path = root / relative
    original = path.read_bytes()
    alternate = path.with_name("alternate_" + path.name)
    for operation in ("add", "edit", "rename", "delete"):
        if operation == "add":
            alternate.write_text("new selected input")
        elif operation == "edit":
            path.write_text("changed selected input")
        elif operation == "rename":
            path.rename(alternate)
        else:
            path.unlink()
        observed = identities(root)
        assert {name for name in COMPONENTS if observed[name] != baseline[name]} == DYNAMIC[relative], (relative, operation)
        alternate.unlink(missing_ok=True)
        path.write_bytes(original)


@pytest.mark.parametrize("relative", FIXED)
def test_required_input(identity_tree: tuple[Path, dict[str, str]], relative: str) -> None:
    """Editing a mandatory input invalidates exact components; deleting or renaming it fails closed."""
    root, baseline = identity_tree
    path = root / relative
    path.write_text("changed required input")
    observed = identities(root)
    assert {name for name in COMPONENTS if observed[name] != baseline[name]} == FIXED[relative], relative
    path.unlink()
    with pytest.raises(ValueError, match="does not exist"):
        identities(root)
    path.write_text("required input before rename")
    path.rename(path.with_name("renamed_" + path.name))
    with pytest.raises(ValueError, match="does not exist"):
        identities(root)


@pytest.mark.parametrize("parent", PARENTS)
def test_generated_tree_invariance(identity_tree: tuple[Path, dict[str, str]], parent: str) -> None:
    """All generated directory categories beneath this component remain outside every source identity."""
    root, baseline = identity_tree
    for ignored in IGNORED:
        folder = root / parent / ignored
        folder.mkdir()
        for suffix in ("lean", "py", "c", "h", "y", "json", "sql"):
            (folder / f"output.{suffix}").write_text("generated output")
    assert identities(root) == baseline


@pytest.mark.parametrize("relative", ["README.md", "docs/notes.md", "build-support/notes.md"])
def test_unselected_file_invariance(identity_tree: tuple[Path, dict[str, str]], relative: str) -> None:
    """Unrelated documentation does not invalidate any build component."""
    root, baseline = identity_tree
    (root / relative).parent.mkdir(parents=True, exist_ok=True)
    (root / relative).write_text("unselected input")
    assert identities(root) == baseline


def test_model_change_reaches_the_conformance_runtime(
        identity_tree: tuple[Path, dict[str, str]]) -> None:
    """The actual Nix entrypoint binds the model into the conformance runtime, and a change to the
    conformance runner leaves the model alone."""
    root, _ = identity_tree
    def derivations() -> dict[str, str]:
        """Evaluate the production dependency graph with a private source root, without building it."""
        literal = json.dumps(str(root)).replace('${', '\\${')
        expression = ('let builds = import ./build-support/default.nix { root = /. + ' + literal + '; }; '
                      'in builtins.mapAttrs (_: value: value.drvPath) { '
                      'inherit (builds) modelPackage conformanceRuntime; }')
        result = run_command(['nix-instantiate','--eval','--strict','--json',
            '--extra-experimental-features','nix-command flakes','--expr',expression],cwd=ROOT,timeout=30)
        assert result.returncode == 0, result.diagnostic()
        return json.loads(result.stdout)
    before = derivations()
    runner = root / 'packages/verifier-conformance/ConformanceRunner.lean'
    original = runner.read_bytes()
    runner.write_bytes(original+b'\nrunner-only change\n')
    changed = derivations()
    assert changed['modelPackage'] == before['modelPackage']
    assert changed['conformanceRuntime'] != before['conformanceRuntime']
    runner.write_bytes(original)
    model = root / 'packages/belay-sqlite-model/Belay/Sqlite/Model/Shared/Catalog/Database.lean'
    model.write_bytes(model.read_bytes()+b'\nmodel change\n')
    changed = derivations()
    assert all(changed[name] != before[name] for name in before)
