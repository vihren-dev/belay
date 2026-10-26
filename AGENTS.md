# Agent instructions for sqlite-verifier

The workspace rules in the parent directory's `AGENTS.md` also apply. This
file adds rules that are specific to this repository.

## Writing style

All text in this repository follows these style guides:

1. [ASD-STE100 Simplified Technical English](https://www.asd-ste100.org/):
   its writing rules. Its dictionary is not required.
2. [Google developer documentation style guide](https://developers.google.com/style):
   for everything ASD-STE100 does not cover, including error messages and how
   to refer to code, files and commands in text.

When the two conflict, ASD-STE100 applies.

"Text" means documentation, comments, docstrings, commit messages, and strings
that users see: CLI output, diagnostics and error messages.

Rules for this repository:

- Write each document for one audience: users (README, package READMEs,
  examples), designers and reviewers (ADRs), or the team
  (status and acceptance records). Do not mix them in one document.
- A docstring tells what the code does and why. Use a negative statement only
  to warn about a real trap.
- An error message tells what failed, where, and what the user can do next.
  Do not refer to internal documents, such as ADR numbers, in user-facing text.

## Goal, core and supporting code

The goal of this repository is a semantic model of SQLite as a Lean library:
Lean developers state and prove facts about SQLite databases, statements and
queries, and can trust that the model behaves as SQLite does, which the
conformance evidence checks against native SQLite.

Core code is the model and the evidence that it agrees with SQLite. It must
serve the goal, and a specification may plan it ahead. Supporting code is
everything else: tooling, CI, harness features, measurement scripts, process
automation and refactors that no core change needs. Write supporting code only
to solve a clear present problem, with the smallest change that solves it. A
present problem exists now: a failing check, a measured cost, a core task that
it blocks, or an owner request. "Later", "at scale", "for consistency" and "in
case" are not present problems. Review condition R18 checks this in
specifications.

## Replaced code

The project has no users. When code is replaced, update all callers and delete
the old code. Do not keep compatibility paths, and do not mark code as "legacy".
Do not keep aliases for replaced names or fall back to a replaced path.

Review this rule again before the first public release, when users and
compatibility matter. Historical evidence and the readers needed to replay it
are retained; they are not replaced implementation paths.

## Lean maintenance

Until the project has users, follow each stable Lean release. Upgrade within
two weeks after a stable release, in its own change, with no other work in it.
Do not adopt release candidates. If a Lean dependency (doc-gen4) has no tag
for the new version, try to build its latest tag under the new version; if
that fails, record it in the upgrade issue and wait for the dependency. Do not downgrade the toolchain automatically.

This policy covers the Lean toolchain and the Lean dependencies built with it.
It excludes the SQLite versions in the execution profiles: those versions
define verification semantics and change only as product decisions.

Review this policy when the project gets its first users. Upgrades must then
also consider compatibility of user proofs.

## Checked public documentation

A change to a public declaration updates its docstring in the same commit.
Docstrings of public Lean declarations and their fields use Verso format.
Enable it with `set_option doc.verso true` for the file or declaration, so Lean
checks the documentation when it compiles the code.

Write these docstrings for library users: state the meaning, give an example,
and say which value to use when the user does not need the feature. Names use
checked `{name}` references. Terms and code examples use checked `{lean}` terms
or `lean` code blocks. Use `{assert}` for computed facts that Lean can check by
definitional equality.

Checked references cannot refer to declarations defined later in the same file.
Place each referenced declaration before the docstring that uses it, or put
the walkthrough in a module docstring at the end of the file. A plain code span
is not a checked reference.

## Propositions in plain words

A proof certifies only the formula as written. If the formula says less than
intended, verification still succeeds. The plain-words statement is where a
reader checks that the formula and the intent agree.

- Each proposition in the core library and the public API has a docstring that
  restates it in plain words: each `def` or `abbrev` of type `Prop`, each field
  of type `Prop` in a structure, and each theorem statement. A small internal
  helper lemma needs one sentence.
- The words say what the formula says, not what it is meant to say. Include
  the quantifiers, what is assumed and what follows, and each case in which
  the formula requires nothing. If the formula is weaker than the intent, say
  so.
- The structure of the text follows the formula: one item for each conjunct or
  case.
- Declaration names in the statement use checked `{name}` references.
- A change to a formula changes its plain-words statement in the same commit.
- Proofs need no restatement: the kernel checks them, and trust does not
  depend on them. Exception: a library theorem that other proofs use, or a
  proof longer than about 20 lines, has a short proof sketch (1-5 sentences)
  in its docstring. The sketch describes the strategy and the key idea, not
  each step.

## Testing

A test is useful only when we know what it checks. These rules apply to new
and changed tests and checks, including checks that tools run during a build.

- **Name the subject.** The docstring of a test says which code of this
  repository it checks, or which known problem of a dependency it checks, and
  why.
- **Test our code.** Tests check our code, our configuration and our use of
  dependencies. They do not check a dependency's own behavior, except for a
  suspected problem, as the next rules describe. For example, a
  check of the links that doc-gen4 writes on Lean's library pages tests
  doc-gen4, not this repository.
- **Dependency as oracle.** A dependency can supply the expected result for
  our code. The conformance corpus uses native SQLite in this way. Such a test
  checks our code and is not a test of the dependency.
- **Check a dependency only for a suspected problem.** Do not keep a test of a
  dependency in the test suite or in CI if there is no reason to suspect that
  the test can fail. A dependency upgrade alone is no such reason: we do not
  run a dependency's own test suite. A check of a dependency names the known
  or suspected problem, as an upstream report or an observed failure, and is
  removed when the problem is gone. A check that the pinned Lean and SQLite
  builds are the ones in use tests our configuration, not the dependency.
- **Workarounds are narrow.** A workaround for a dependency bug covers only the
  cases that we need, names the upstream report, and is removed when the fix
  arrives.

## The local build loop

direnv loads the development shell of `shell.nix` when a session changes into
the repository. Run `just`, `lake` and `python3` directly. Do not start a shell
with `nix develop` or `nix-shell`. If `just dev-build` says that the shell is
not loaded, ask the owner to run `direnv allow` in the workspace.

- While you edit the Lean packages under `packages/`, check each edit with
  `just dev-build`. When the edit can change a prediction, also run
  `just dev-verdict`, for all corpora or for the ones that the edit touches.
- Before each commit, run the checks that "Checks and their cadence" gives for
  a commit.
- A local result is not evidence (ADR 0011, ADR 0020). Commit messages, status
  files and pull requests cite only results of the Nix checks.

## Checks and their cadence

`just test-full` takes about 15 minutes. Run each check at the point that this
table gives, and not more frequently.

| When | Checks |
| --- | --- |
| Each edit of `packages/` | `just dev-build`. Also `just dev-verdict` when the edit can change a prediction. |
| Each commit | The tests that touch the change, for example its test files with `python3 -m pytest`, then `just review`. The status file names the tests. |
| End of each slice of the task file | After the review of the slice's last commit: `just test-full`, `just verdict`, and the mutant tests of the mutant tables that the slice adds or changes. |
| End of the task, before its pull requests | `just test-nix` and `just test-scheduled-checks`, once. |

Rules for the time while checks run:

- Do not wait for a check without work. While a check runs, start the next
  step in a second jj workspace. Remove the workspace when its commits are in
  the main line.
- A question to the owner does not stop the work. Continue with the work that
  does not need the answer. Stop only when no such work remains.
- Run only the mutant tests that a change touches, by name, for example
  `python3 -m pytest tests/conformance_query_mutants_test.py -k parameter`. Do not run
  the mutant suites locally (`just test-scheduled` or `just test-mutants`): they overload
  the machine, and CI runs all of them every day.
- Before `just review`, check the change yourself against R3 (proof sketches)
  and R19 (specifications against current reality). Most "must" findings come
  from these two conditions.

## Development claims

The verdict job checks the claims in `judge/claims.json` against the frozen
corpora (ADR 0011). A task that changes a claim, a corpus, the judge or the
native SQLite oracle has two pull requests:

1. The judge change with its new `integrity/judge.lock.json` (`just judge-lock`).
   It needs the owner's approval.
2. The work, for example model changes, which does not change the lock.

Do not put recorded SQLite results of corpus cases into the subject's code
(review condition R17).

## Review after each commit

An independent reviewer checks each commit against
[`docs/review-checklist.md`](docs/review-checklist.md). The reviewer is the other
agent tool: Codex reviews commits from Claude Code sessions, and Claude Code
reviews commits from Codex sessions.

- After each commit whose checks pass, run `just review`. It reviews `@-`, the
  commit before the working copy. A commit that changes only status files
  (`plans/*.status.md`) or review records needs no review. A commit that adds or
  changes a specification, such as an ADR or a task file, gets a review like any
  other commit (conditions R18 and R19).
- Exit code 0: no "must" findings. Fix "should" findings, or reject or defer
  them with a reason.
- Exit code 1: fix each "must" finding in a `refactor:` commit before the next
  feature commit, and review that commit too. After four review rounds in a row
  with new "must" findings, stop and report to the owner.
- Record the outcome of every finding with
  `just review-resolve FINDING-ID fixed`, or `rejected "REASON"`, or
  `deferred "REASON"`. `just review` prints the finding ids. Reject a finding
  when it is wrong, and say why.
- `just review` and `just review-resolve` each add one new record file under
  `reviews/`. Commit the new files with your next commit. Do not edit or delete
  record files.
- The owner uses `just review-stats` to find conditions that never fire, are
  mostly rejected, or that nobody acts on, and removes or rewrites them.
- Exit code 2: the command cannot choose a reviewer or revision; follow its
  message (for example, set `REVIEWER=claude` or `REVIEWER=codex`).
- Exit code 3: the reviewer failed or gave no recognizable result. Run the
  review once more; if it fails again, record it and tell the owner.
- A reviewer never starts `just review`; the command stops if it is called
  inside a review.
