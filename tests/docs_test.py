"""Check local destinations in authored Markdown without downloading linked pages."""

from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]


def broken_links(root: Path) -> list[str]:
    """Check current documentation; historical plans retain links to their original source layout."""
    errors: list[str] = []
    paths = [*root.glob("*.md"), *root.glob("docs/**/*.md")]
    for path in paths:
        text = path.read_text()
        inline = re.findall(r"\[[^\]]*\]\(([^)]+)\)", text)
        definitions = re.findall(r"^\[[^\]]+\]:\s+(\S+)", text, re.M)
        for found in [*inline, *definitions]:
            target = found.split(' "', 1)[0].strip("<>")
            url = urlsplit(target)
            if not url.scheme and url.path and not url.path.startswith("/"):
                if not (path.parent / unquote(url.path)).exists():
                    errors.append(f"{path.relative_to(root)}: missing {target}")
    return errors


def test_broken_links_detects_missing_local_files(tmp_path: Path) -> None:
    """Missing local files are reported; external URLs and anchors are outside this bounded check."""
    (tmp_path / "README.md").write_text("[file](missing.md) [web](https://example.org) [anchor](#x)")
    assert broken_links(tmp_path) == ["README.md: missing missing.md"]
    (tmp_path / "missing.md").write_text("present")
    assert broken_links(tmp_path) == []
    (tmp_path / "docs/nested").mkdir(parents=True)
    (tmp_path / "docs/nested/guide.md").write_text("[broken](absent.md)")
    assert broken_links(tmp_path) == ["docs/nested/guide.md: missing absent.md"]


def test_local_markdown_links() -> None:
    """Current documentation links resolve while historical plan records keep their original paths."""
    assert broken_links(ROOT) == []


def test_reference_definitions_are_checked(tmp_path: Path) -> None:
    """`broken_links` also reads the destinations of reference definitions (`[name]: path`)."""
    (tmp_path / "README.md").write_text("[text][name]\n\n[name]: missing.md\n[web]: https://example.org\n")
    assert broken_links(tmp_path) == ["README.md: missing missing.md"]


USER_DOCS = {"README.md", "cheat-sheet.md", "execution-profile.md", "faq.md", "semantic-subset.md", "guide", "media"}
"""The index, the pages for users of the library and their folders, at the top level of `docs/`."""

INTERNAL_DOCS = {"adr", "development", "records"}
"""The folders of `docs/` for design records, development pages and dated records."""


def test_docs_top_level_holds_only_user_pages() -> None:
    """The layout of `docs/` in this repository: a visitor finds only pages for users at the top
    level. A new development page or record belongs in one of the folders of `INTERNAL_DOCS`; a
    new user page is added to `USER_DOCS` and to the index `docs/README.md`."""
    assert {path.name for path in (ROOT / "docs").iterdir()} == USER_DOCS | INTERNAL_DOCS


def test_historical_plan_links_are_exempt(tmp_path: Path) -> None:
    """A removed historical source path is allowed in plans but still rejected in current docs."""
    (tmp_path / "plans").mkdir()
    (tmp_path / "plans/historical.status.md").write_text("[old source](../removed.lean)")
    assert broken_links(tmp_path) == []
    (tmp_path / "docs").mkdir()
    (tmp_path / "docs/guide.md").write_text("[source](../removed.lean)")
    assert broken_links(tmp_path) == ["docs/guide.md: missing ../removed.lean"]


if __name__ == "__main__":
    failures = broken_links(ROOT)
    print("\n".join(failures) or "Current documentation links resolve; historical plans, external URLs and anchors are not checked.")
    sys.exit(1 if failures else 0)


REMOVED_PRODUCT_TERMS = ("ADR ", "approved contract", "migration framework", "SQLx", "formatVersion")
"""Terms of the removed verifier product, design records and recorder transport (#19)."""


def test_execution_profile_document_is_for_library_users() -> None:
    """`docs/execution-profile.md` is a user document: it uses none of the vocabulary of the removed
    verifier product, refers to no design record and leaves the recorder format to
    `docs/development/native-corpus-format.md`."""
    text = (ROOT / "docs/execution-profile.md").read_text()
    assert [term for term in REMOVED_PRODUCT_TERMS if term in text] == []
