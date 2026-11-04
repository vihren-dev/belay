"""The slice check: a tokenizer cut compiles to the same code as the whole `sqlite3.c`.

`parser/tokenizer_cut.py` takes the tokenizer out of a release's amalgamation by name. This
check compiles the library's tokenizer unit twice, once with the cut and once with the
whole file, and requires that each function and table of the cut's object has the same
machine code or bytes as the one of the same name in the full object, with relocations
compared by symbol name and string literals by content (ADR 0029, D2). It also requires that
the cut's object defines no global symbol except the wrapper functions of
`parser/tokenizer.c`.

The units are compiled at `-O0`: at the library's `-O1` the compiler inlines a static
function with one caller, and `keywordCode` has two callers in `sqlite3.c` but one in the
cut. The check runs once, in the generation, on Linux: it reads ELF sections with `objdump`.
"""

from pathlib import Path
import re
import subprocess
import tempfile

TOOL_TIMEOUT_SECONDS = 300
"""The limit for one compile of the whole amalgamation or one `objdump` run."""
CHECK_PREFIX = "Tokenizer_check"
"""The wrapper prefix of both compiled units."""
COMPARED_SECTION = re.compile(r"\.(?:text|rodata|data)\.")
"""The sections of one function or one table, which `-ffunction-sections` and
`-fdata-sections` give."""
LITERAL = re.compile(r"\.rodata(?:\.str[\w.]*)?([+-])0x([0-9a-f]+)")
"""A relocation to a string literal; the offset differs between the two objects."""
WRAPPER_FUNCTIONS = frozenset(f"{CHECK_PREFIX}_{name}" for name in
                              ("native_token", "native_name", "native_space", "native_illegal",
                               "native_semicolon"))
"""The only global symbols of a tokenizer object: the functions of `parser/tokenizer.c`."""


def _run(command: list[str]) -> str:
    """Run a tool and return its output; fail with the tool's message."""
    result = subprocess.run(command, capture_output=True, text=True, timeout=TOOL_TIMEOUT_SECONDS)
    if result.returncode != 0:
        raise ValueError(f"{command[0]} failed in the slice check:\n{result.stderr}")
    return result.stdout


def compile_unit(compiler: str, flags: list[str], source: Path, includes: list[Path], output: Path) -> Path:
    """Compile the tokenizer unit at `-O0` with the folder that holds `sqlite3_tokenizer.c`
    first; the optimization flags of `flags` are left out."""
    _run([compiler, "-c", "-O0", "-ffunction-sections", "-fdata-sections",
          *(flag for flag in flags if not flag.startswith("-O")),
          f"-DTOKENIZER_PREFIX={CHECK_PREFIX}", *(f"-I{folder}" for folder in includes), str(source),
          "-o", str(output)])
    return output


def sections(obj: Path) -> list[str]:
    """Return the names of the sections of an object."""
    return re.findall(r"^\s*\d+\s+(\S+)", _run(["objdump", "-h", "-w", str(obj)]), re.M)


def _rodata(obj: Path) -> bytes:
    """Return the bytes of the object's `.rodata` section, which holds its string literals."""
    with tempfile.TemporaryDirectory() as folder:
        _run(["objcopy", "-O", "binary", "--only-section=.rodata", str(obj), f"{folder}/rodata"])
        return Path(folder, "rodata").read_bytes()


def section_text(obj: Path, section: str) -> str:
    """Return the disassembly or bytes of one section, with its relocations and literals."""
    form = ["-d", "--no-addresses"] if section.startswith(".text") else ["-s"]
    text = _run(["objdump", *form, "-r", "-w", "-j", section, str(obj)]).split("\n", 3)[3]
    data = _rodata(obj)

    def literal(match: re.Match[str]) -> str:
        """The string that a relocation addresses; x86-64 addends are 4 bytes before it."""
        offset = int(match.group(2), 16) * (1 if match.group(1) == "+" else -1) + 4
        return repr(data[offset:data.index(b"\0", offset)])
    return LITERAL.sub(literal, text)


def global_symbols(obj: Path) -> set[str]:
    """Return the names of the global symbols that the object defines."""
    return {line.split()[-1] for line in _run(["nm", "-g", "--defined-only", str(obj)]).splitlines() if line}


def differences(cut: Path, full: Path) -> list[str]:
    """One line for each section of the cut object that differs from the full object."""
    full_sections = set(sections(full))
    found = []
    for section in (name for name in sections(cut) if COMPARED_SECTION.match(name)):
        if section not in full_sections:
            found.append(f"{section}: not in the object of the whole sqlite3.c")
        elif section_text(cut, section) != section_text(full, section):
            found.append(f"{section}: differs from the object of the whole sqlite3.c")
    extra = global_symbols(cut) - WRAPPER_FUNCTIONS
    if extra:
        found.append(f"global symbols other than the wrapper's: {sorted(extra)}")
    return found


def check_slice(compiler: str, flags: list[str], parser: Path, cut_folder: Path, amalgamation: Path) -> int:
    """Compile the unit with the cut and with the amalgamation; fail on any difference.

    `cut_folder` holds `sqlite3_tokenizer.c` and `token_names.inc`. Returns the number of
    sections compared.
    """
    with tempfile.TemporaryDirectory() as work:
        full_folder = Path(work, "full")
        full_folder.mkdir()
        (full_folder / "sqlite3_tokenizer.c").write_bytes(amalgamation.read_bytes())
        (full_folder / "token_names.inc").write_bytes((cut_folder / "token_names.inc").read_bytes())
        source = parser / "library_tokenizer.c"
        cut = compile_unit(compiler, flags, source, [cut_folder, parser], Path(work, "cut.o"))
        full = compile_unit(compiler, flags, source, [full_folder, parser], Path(work, "full.o"))
        found = differences(cut, full)
        if found:
            raise ValueError("The tokenizer cut does not compile to the code of the whole sqlite3.c; "
                             "add the missing names to parser/tokenizer_cut.py:\n" + "\n".join(found))
        return sum(1 for name in sections(cut) if COMPARED_SECTION.match(name))
