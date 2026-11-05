"""Consume the existing Belay proof-cost report without extending its collector."""

import json
from pathlib import Path
import shutil

from probe_support import run, write_json


def measure(root: Path, output: Path) -> None:
    """Compile the unchanged collector modules and check fresh, reused and stale data."""
    output.mkdir()
    work = output / "work"
    destination = work / "Belay/Sqlite"
    destination.mkdir(parents=True)
    source = root / "packages/belay/Belay/Sqlite"
    for path in [*source.glob("ProofCost*.lean"), source / "SqlSourceRecord.lean"]:
        shutil.copyfile(path, destination / path.name)
    for name in ("CostFixture.lean", "ReadCosts.lean"):
        shutil.copyfile(Path(__file__).with_name(name), work / name)
    modules = sorted("Belay.Sqlite." + path.stem for path in destination.glob("*.lean"))
    (work / "lakefile.toml").write_text('name = "cost-probe"\n'
        '[[lean_lib]]\nname = "Belay"\nroots = ' + json.dumps(modules) + '\n'
        '[[lean_lib]]\nname = "CostFixture"\n')
    run(output, "build", ["lake", "--no-cache", "build", "CostFixture", "Belay"], cwd=work, timeout=90)
    first = run(output, "report", ["lake", "env", "lean", "--run", "ReadCosts.lean"], cwd=work)
    report = json.loads(first.stdout)
    records = report["libraries"][0]["records"]
    assert len(records) == 1 and records[0]["declaration"] == "counted"
    assert records[0]["status"] == "completed" and isinstance(records[0]["heartbeats"], int)
    repeated = run(output, "repeat", ["lake", "env", "lean", "--run", "ReadCosts.lean"], cwd=work)
    assert repeated.stdout == first.stdout
    with (work / "CostFixture.lean").open("a") as stream:
        stream.write("\n/- Changed after compilation to demonstrate stale measurement detection. -/\n")
    stale = run(output, "stale", ["lake", "env", "lean", "--run", "ReadCosts.lean"], cwd=work, expected=None)
    assert stale.returncode != 0 and "stale" in stale.stdout
    write_json(output / "summary.json", {"records": records, "repeat_identical": True,
        "stale_exit": stale.returncode, "unit": report["unit"],
        "scope": "Existing optional collector, body elaboration only; not kernel checking or runtime coverage.",
        "collection_requires_opt_in_import": True})
