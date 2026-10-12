"""Command-line parts of the proof author's commands (ADR 0010 sections 1 and 10).

`prepare` runs every phase; `init` creates a proofs project; `generate`, `check`,
`audit` and `export` run one phase each, so the loop after a proof edit runs only
`check` (or `lake build`); `clean-cache` removes other builds' cache folders.
"""

import argparse
from collections.abc import Callable
import importlib
from pathlib import Path

ArgumentAdder = Callable[[argparse.ArgumentParser], None]
"""Adds shared arguments to one command's parser."""

COMMANDS: dict[str, tuple[str, str]] = {
    "prepare": ("prepare", "prepare"), "generate": ("prepare", "generate"),
    "export": ("prepare", "export_bundle_command"), "check": ("project_phases", "check"),
    "audit": ("project_phases", "audit"), "init": ("init_project", "init_project"),
    "clean-cache": ("cache_commands", "clean_cache"),
}
"""Command name to (module, function); modules load only when their command runs."""

SUCCESS = frozenset({"PREPARED", "GENERATED", "CHECKED", "AUDITED", "INITIALIZED", "CLEANED"})
"""Statuses of a successful proof-author command; each exits 0."""


def add_project_commands(commands: argparse._SubParsersAction, guide: str, contract: ArgumentAdder,
                         cache: ArgumentAdder, input_help: dict[str, str]) -> None:
    """Add the proof author's commands; `contract` adds the SQL and contract inputs, `cache` the cache options."""
    def command(name: str, summary: str, description: str) -> argparse.ArgumentParser:
        """One command with the shared help layout and output format."""
        parser = commands.add_parser(name, help=summary, description=description, epilog=guide,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
        return parser

    def project(parser: argparse.ArgumentParser) -> None:
        """The proofs project folder."""
        parser.add_argument("--project", required=True, type=Path,
                            help="Proofs project: a Lake project with NextInterpretation.lean and Proofs.lean (see init)")

    for name, summary, description in (
            ("prepare", "Build the proofs project and export a proof bundle (agent side)",
             "Generate, build, audit and export the candidate's proofs project with Lake. PREPARED records that "
             "the bundle was written."),
            ("generate", "Write the generated modules into the proofs project",
             "Write SchemaInputs, SqlInputs, Generated and the audit module Check from the SQL; unchanged files "
             "are left alone."),
            ("export", "Write the proof bundle from the built proofs project",
             "Export the built proofs for verify-bundle, without the audit; prepare audits before it exports.")):
        parser = command(name, summary, description)
        contract(parser)
        project(parser)
        if name in ("prepare", "export"):
            parser.add_argument("--output", required=True, type=Path, help="Bundle file to write")
        cache(parser)
    for name, summary, description in (
            ("check", "Build the proofs project (the loop after each proof edit)",
             "Build the project's default targets with Lake; the same as lake build in the project."),
            ("audit", "Check the proofs for axioms and imports the verifier rejects",
             "Build the generated audit module Check; a failure names the theorem, axiom or module.")):
        parser = command(name, summary, description)
        project(parser)
        parser.add_argument("--format", choices=("human", "json"), default="human")
        cache(parser)
    init = command("init", "Create a proofs project around a candidate's Lean files",
                   "Write a starting lakefile.toml, lean-toolchain and the .belay/runtime link into a folder that "
                   "holds NextInterpretation.lean and Proofs.lean.")
    init.add_argument("--project", required=True, type=Path, help="Folder of the candidate's Lean files")
    for name in ("requirements", "interpretation"):
        init.add_argument("--" + name, required=True, type=Path, help=input_help[name])
    init.add_argument("--format", choices=("human", "json"), default="human")
    clean = command("clean-cache", "Remove cache folders of other verifier builds",
                    "Remove the subfolders of the default Lake cache that belong to other verifier builds; the "
                    "current build's folder stays.")
    clean.add_argument("--format", choices=("human", "json"), default="human")


def run_project_command(options: argparse.Namespace) -> dict[str, object]:
    """Run the selected proof-author command."""
    module, function = COMMANDS[options.command]
    run: Callable[..., dict[str, object]] = getattr(importlib.import_module(f"migration_check.{module}"), function)
    return run() if options.command == "clean-cache" else run(options)


def human_lines(result: dict[str, object]) -> list[str]:
    """Plain-text output of a successful proof-author command: its warnings, then one result line."""
    lines = [f"warning: {warning}" for warning in result.get("warnings", [])]  # type: ignore[union-attr]
    status = result["status"]
    detail = {"PREPARED": result.get("bundle"), "INITIALIZED": result.get("lakefile"),
              "CLEANED": f"{len(result.get('removed', []))} folders",  # type: ignore[arg-type]
              "GENERATED": f"{len(result.get('written_modules', []))} modules written",  # type: ignore[arg-type]
              }.get(str(status), f"{len(result.get('compiled_modules', []))} modules compiled")  # type: ignore[arg-type]
    return [*lines, f"{status}: {detail}"]
