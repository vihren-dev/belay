"""Write a portable dependency browser with no network or server requirement."""

import json
from pathlib import Path


def write_report(data: dict[str, object], output: Path) -> None:
    """Embed the exported graph and local assets without interpreting source as HTML."""
    if data.get("schemaVersion") != 1:
        raise ValueError("Cannot write dependency report: expected schemaVersion 1.")
    for field in ("modules", "declarations", "external"):
        if not isinstance(data.get(field), list):
            raise ValueError(f"Cannot write dependency report: {field} must be a list.")
    assets = Path(__file__).parent
    encoded = json.dumps(data, ensure_ascii=True, separators=(",", ":"))
    # HTML parses script end tags even when their text is inside a JSON string.
    encoded = encoded.replace("<", "\\u003c").replace(">", "\\u003e").replace("&", "\\u0026")
    document = (assets / "theorem_dependency_report.html").read_text(encoding="utf-8")
    for name in ("style.css", "graph.js", "ui.js", "views.js"):
        document = document.replace(f"<!-- {name} -->", (
            assets / f"theorem_dependency_{name}").read_text(encoding="utf-8"))
    document = document.replace("<!-- graph-data -->", encoded)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(document, encoding="utf-8")
