# Task: a `docs/` folder that separates user pages from internal pages

Date: 2026-11-17. Status: OPEN. Owner request of 2026-11-17.
Audience: the implementer and the reviewer.

## The problem

`docs/` holds about 70 files at one level: 32 design records (`adr-*.md`),
about 36 development and evidence pages, and three pages for users of the
library. A visitor who opens `docs/` cannot find the user pages, and cannot see
which pages describe the current state. Some pages are out of date and do not
say so.

## What is true when the task is done

1. The top level of `docs/` holds only pages for users of the library, the
   index, and folders:

   | Path | Contents |
   | --- | --- |
   | `docs/README.md` | The index. |
   | `docs/cheat-sheet.md`, `docs/execution-profile.md`, `docs/semantic-subset.md`, `docs/guide/`, `docs/media/` | Pages for users. |
   | `docs/adr/` | The design records `adr-*.md`. |
   | `docs/development/` | Pages that describe how the repository works now: CI, the review checklist, the conformance formats and tools, the parser boundary. |
   | `docs/records/` | Dated findings, inventories and plans that describe a past state. |

2. `docs/README.md` has two lists. "Use Belay" names each user page with one
   line. "Development" names the three folders, says which describe the
   current state, and says that a record is true only for its date.
3. A page that is out of date says so in a status line below its title. The
   line gives the date of the page and where the current information is.
4. Each relative link in current Markdown resolves: the top-level `*.md`
   files, `docs/**`, package READMEs, `build-support/README.md` and the skill.
5. Each path to a moved page in current code and configuration is the new
   path: tools, tests, the justfile, Nix files, CODEOWNERS, Python and Lean
   docstrings.
6. `just review` works: it reads the checklist at its new path.

## Tests

- `python3 -m pytest tests/docs_test.py`: the link check covers the top-level
  files and `docs/**`. It also has a test that the top level of `docs/` holds
  only the files of item 1, so that a new development page cannot land there.
- `python3 -m pytest tests/test_review.py tests/restriction_registry_test.py`
  and the tests of the review log: the tools read the pages at the new paths.
- The Nix checks at the end of the task (`just test-nix`,
  `just test-scheduled-checks`) cover the Nix file that names the checklist.

## Points to be careful about

- `plans/`, `reports/`, `reviews/`, `experiments/` records and
  `research_notes/` are history. They keep the paths of their date;
  `tests/docs_test.py` already exempts plans from the link check. Exception:
  `experiments/observability/default.nix` reads the checklist as a source file
  and must name the new path.
- `judge/__init__.py` names the path of a design record in its docstring. The
  judge lock covers that file (`integrity/judge.nix`), so its change is a
  separate pull request with a new `integrity/judge.lock.json`, which needs the
  owner's approval.
- A link inside a moved page is relative to the page. A move one level down
  changes each link to a file outside the new folder.
- `tests/ci_scope.py` gives a change of only Markdown the scope `docs`. This
  task also changes code, so CI runs the full checks.
- `AGENTS.md` (and `CLAUDE.md`, a link to it) names two of the moved pages.
- The four new user pages of the launch plan (supported SQL, trust, questions
  and answers, limitations) are not part of this task.
