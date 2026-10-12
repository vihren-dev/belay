"""The user's proofs project: a Lake project that `prepare` builds as it is (ADR 0010 sections 1 and 10).

The project has the user's own `lakefile.toml` and `lean-toolchain`. The tool
owns two things in it: the folder `Generated/`, which it rewrites from the SQL,
and the symbolic link `.belay/runtime`, which points at the installation, so the
lakefile can require the verifier's library by a path that is the same on every
machine. `prepare` runs in the agent's trust domain and does not judge the
project; `verify-bundle` does.
"""

from collections.abc import Iterable, Mapping
import json
import os
from pathlib import Path
import tomllib

RUNTIME_LINK = Path(".belay/runtime")
"""Project-relative link to the installation; the lakefile requires the library through it."""

GENERATED_FOLDER = "Generated"
"""Project folder that the tool rewrites; nobody edits it by hand."""

GENERATED_MODULES = ("SchemaInputs", "SqlInputs", "Generated")
"""Modules that the tool writes into `Generated/` and that the default build compiles."""

AUDIT_LIBRARY, AUDIT_MODULE = "Audit", "Check"
"""The generated module that audits the proofs, and its library; it is not a default target, so the
per-edit check does not pay for loading `Lean` (ADR 0010 section 10)."""


def link_runtime(project: Path, runtime_root: Path) -> None:
    """Point `.belay/runtime` at the installation, replacing a link to another one."""
    link = project / RUNTIME_LINK
    link.parent.mkdir(parents=True, exist_ok=True)
    if link.is_symlink() and Path(os.readlink(link)) == runtime_root:
        return
    if link.is_symlink() or link.exists():
        link.unlink()
    link.symlink_to(runtime_root, target_is_directory=True)


def write_generated(project: Path, sources: Mapping[str, str]) -> list[str]:
    """Write each generated module whose content changed; return their names.

    An unchanged file is not rewritten, so generation never causes a rebuild by itself.
    """
    folder = project / GENERATED_FOLDER
    folder.mkdir(exist_ok=True)
    written = []
    for module, text in sources.items():
        path = folder / f"{module}.lean"
        if not path.is_file() or path.read_text(encoding="utf-8") != text:
            path.write_text(text, encoding="utf-8")
            written.append(module)
    return written


def project_lakefile(name: str, contract_folder: str, contract_modules: Iterable[str],
                     candidate_modules: Iterable[str]) -> str:
    """A starting lakefile: the contract read in place, the generated modules, and the candidate modules."""
    libraries = (("Contract", contract_folder, list(contract_modules)),
                 ("GeneratedInputs", GENERATED_FOLDER, list(GENERATED_MODULES)),
                 ("Candidate", ".", list(candidate_modules)))
    lines = [f"name = {json.dumps(name)}", f"defaultTargets = {json.dumps([lib for lib, _, _ in libraries])}",
             "enableArtifactCache = true", "restoreAllArtifacts = true", "",
             "[[require]]", 'name = "sqliteVerifier"', f"path = {json.dumps(RUNTIME_LINK.as_posix())}"]
    for library, folder, roots in (*libraries, (AUDIT_LIBRARY, GENERATED_FOLDER, [AUDIT_MODULE])):
        lines += ["", "[[lean_lib]]", f"name = {json.dumps(library)}", f"srcDir = {json.dumps(folder)}",
                  f"roots = {json.dumps(roots)}"]
    return "\n".join(lines) + "\n"


def listed_modules(lakefile_text: str) -> tuple[set[str], tuple[str, ...]]:
    """Module names that a TOML lakefile's libraries list, and their `globs` prefixes (`X.*`, `X.+`)."""
    data = tomllib.loads(lakefile_text)
    names: set[str] = set()
    prefixes: list[str] = []
    for library in data.get("lean_lib", []):
        names.update(library.get("roots", [library.get("name", "")]))
        for pattern in library.get("globs", []):
            if pattern.endswith((".*", ".+")):
                prefixes.append(pattern[:-2])
                if pattern.endswith(".+"):
                    names.add(pattern[:-2])
            else:
                names.add(pattern)
    return names, tuple(prefixes)


def reads_contract_from(lakefile_text: str, project: Path, contract_folder: Path) -> bool:
    """Whether a library of the lakefile reads `Requirements` and `Interpretation` from `contract_folder`.

    Lake builds the contract that the lakefile names; `prepare` must export a bundle for
    the contract it was given, not for another one.
    """
    for library in tomllib.loads(lakefile_text).get("lean_lib", []):
        source = (project / library.get("srcDir", ".")).resolve()
        if source == contract_folder.resolve() and {"Requirements", "Interpretation"} <= set(library.get("roots", [])):
            return True
    return False


CHECK_DISABLING_OPTIONS = ("debug.skipKernelTC",)
"""Lean options that turn off kernel checking; the audit cannot see them, so generation refuses them."""


def turns_on(value: object) -> bool:
    """Whether an option value enables the option; only an explicit false leaves it off."""
    return value not in (False, "false")


def check_disabling_settings(lakefile_text: str) -> list[str]:
    """Where a TOML lakefile turns off checks: enabling `leanOptions` entries and `-D` arguments in
    `moreLeanArgs`/`weakLeanArgs`, for the package and for each library. A setting to false is allowed."""
    data = tomllib.loads(lakefile_text)
    found = []
    for owner, table in [("package", data), *((f"lean_lib {lib.get('name', '?')}", lib)
                                                for lib in data.get("lean_lib", []))]:
        for option in CHECK_DISABLING_OPTIONS:
            options = table.get("leanOptions", {})
            if option in options and turns_on(options[option]):
                found.append(f"{owner}: leanOptions.{option}")
            for key in ("moreLeanArgs", "weakLeanArgs"):
                for argument in table.get(key, []):
                    name, _, value = argument.removeprefix("-D").partition("=")
                    if argument.startswith("-D") and name == option and turns_on(value or "true"):
                        found.append(f"{owner}: {key} {argument}")
    return found


def missing_modules(lakefile_text: str, modules: Iterable[str]) -> list[str]:
    """The modules that no library of the lakefile lists; Lake cannot build or find them."""
    names, prefixes = listed_modules(lakefile_text)
    return [module for module in modules
            if module not in names and not any(module.startswith(prefix + ".") for prefix in prefixes)]
