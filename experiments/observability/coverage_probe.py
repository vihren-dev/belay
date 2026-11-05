"""Compare supported coverage cores and expose missing subprocess test attribution."""

import json
from pathlib import Path

from probe_support import run


def measure(work: Path, output: Path, base: list[str], environment: dict[str, str]) -> dict[str, object]:
    """Compare defaults with documented ctrace, retaining negative results as evidence."""
    summaries: dict[str, object] = {}
    for core in ("default", "ctrace"):
        selected = "" if core == "default" else "core = ctrace\n"
        (work / ".coveragerc").write_text(
            f"[run]\n{selected}branch = true\npatch = subprocess\n[json]\nshow_contexts = true\n")
        label = f"coverage-{core}"
        result = run(output, label, [*base, "-k", "classify or child", "-p", "pytest_cov",
            "--cov=subject", "--cov-context=test", "--cov-report=json:" + str(output / f"{label}.json")],
            cwd=work, environment={**environment, "PROBE_EVENTS": str(output / f"{label}.jsonl")})
        coverage = json.loads((output / f"{label}.json").read_text())
        contexts = coverage["files"]["subject.py"]["contexts"]
        lines = (work / "subject.py").read_text().splitlines()

        def contexts_for(text: str) -> list[str]:
            """Locate fixture lines by their unique text instead of fixed line numbers."""
            number = next(index for index, line in enumerate(lines, 1) if text in line)
            return contexts.get(str(number), [])

        positive = contexts_for('return "positive"')
        zero = contexts_for('return "nonpositive"')
        child = contexts_for('return "child-only"')
        accurate = (positive == ["cases.py::test_classify[positive]|run"]
                    and zero == ["cases.py::test_classify[zero]|run"])
        if core == "ctrace":
            assert accurate, (positive, zero)
        assert child, "subprocess line was not collected"
        summaries[core] = {"positive_contexts": positive, "zero_contexts": zero,
            "child_contexts": child, "parent_test_attribution_correct": accurate,
            "child_has_parent_test_context": any("test_child" in context for context in child),
            "unsupported_context_warning": "no-sysmon-context" in result.stdout + result.stderr,
            "coverage_version": coverage["meta"]["version"]}
    return summaries
