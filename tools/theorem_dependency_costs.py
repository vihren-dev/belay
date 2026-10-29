"""Attach compatible existing proof-cost measurements without instrumenting a build."""

import json
from pathlib import Path

from tools.theorem_dependency_manifest import object_list, object_value


def source_hash(value: object) -> int | None:
    """Accept both JSON encodings of Lean UInt64 while rejecting invalid source identities."""
    if isinstance(value, str) and value.isascii() and value.isdecimal():
        value = int(value)
    return value if type(value) is int and 0 <= value < 2 ** 64 else None


def attach_costs(data: dict[str, object], path: Path | None) -> None:
    """Match S7 records by compiler, module source hash and exact declaration name."""
    data["proofCosts"] = []
    if path is None:
        data["proofCostCoverage"] = {"supplied": False, "attached": 0,
                                    "reason": "No proof-cost file was supplied."}
        return
    document = object_value(json.loads(path.read_text()), str(path))
    modules = {row["name"]: row for row in object_list(data["modules"], "modules")}
    declarations = {row["name"]: row for row in object_list(data["declarations"], "declarations")}
    accepted: list[dict[str, object]] = []
    rejected: list[dict[str, object]] = []
    seen: set[str] = set()
    for library in object_list(document.get("libraries"), f"{path}: libraries"):
        stale = library.get("stale", [])
        if not isinstance(stale, list) or not all(isinstance(name, str) for name in stale):
            raise ValueError(f"{path}: stale must be an array of module names")
        for record in object_list(library.get("records"), f"{path}: records"):
            name, module = record.get("declaration"), record.get("module")
            if not isinstance(name, str) or not isinstance(module, str):
                raise ValueError(f"{path}: proof costs need string declaration and module names")
            source = modules.get(module, {})
            reason = None
            if name not in declarations or declarations[name]["module"] != module:
                reason = "Declaration is outside the selected graph."
            elif record.get("compiler") != data["leanVersion"]:
                reason = "Compiler version differs from the selected graph."
            elif (module in stale or source_hash(source.get("sourceHash")) is None
                  or source_hash(record.get("sourceHash")) != source_hash(source.get("sourceHash"))):
                reason = "Source hash differs or the supplied report marks the module as stale."
            elif (record.get("status") != "completed" or type(record.get("heartbeats")) is not int
                  or record["heartbeats"] < 0):
                reason = "Measurement is incomplete."
            elif (record.get("unit") != "internal-heartbeat" or not isinstance(record.get("scheme"), str)
                  or not record["scheme"]):
                reason = "Measurement unit or scheme is unsupported."
            elif name in seen:
                reason = "Another supplied record already names this declaration."
            if reason:
                rejected.append({"name": name, "reason": reason})
            else:
                accepted.append({**record, "name": name})
                seen.add(name)
    data["proofCosts"] = sorted(accepted, key=lambda record: str(record["name"]))
    data["proofCostCoverage"] = {"supplied": True, "attached": len(accepted), "rejected": rejected}
