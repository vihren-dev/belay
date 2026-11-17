# Questions and answers

Each answer is short and gives one link to the longer text.

## Why not test the migration on a copy of production?

A copy is one database. A claim such as `M preserves Q on shop` is about every
database with the schema, also the rows that the copy does not have yet. The
two work together: `#sql_check` searches for a small database that breaks the
claim and writes it for you, as a test that makes its own fixture, and a proof
then covers the databases that no test reaches. The
[example of the README](../README.md#an-example) is a migration that passes on
an empty database and deletes every session on a database with one customer.

## How do you know that the model is correct?

The model is tested against SQLite, not proved equal to it. The repository
holds 5,525 cases, most of them from SQLite's own test suite, and CI replays
each one against native SQLite 3.51.0 and against the model. One disagreement
fails the build. The cases and the rule are in
[`judge/claims.json`](../judge/claims.json). A proof therefore holds for real
SQLite if the model is faithful on the SQL of the claim. Not every rule of the
model has had a human audit yet. If you find SQL on which the model and SQLite
disagree, [report it](../CONTRIBUTING.md#what-the-project-accepts): that is
the most useful contribution to the project.

## Does a proof that an agent wrote mean anything?

Yes. Lean's kernel checks each step of the proof, so a wrong proof does not
compile, and it does not matter who wrote it. What you must read is the claim,
because a proof of a weak claim is correct and tells you little. `#explain`
prints a claim in plain words, and `#print axioms` shows if a proof has a
hole. [Review the claim, not the proof](guide/agents.md#review-the-claim-not-the-proof)
lists the ways in which a claim can say less than you think.

## Do I have to write Lean?

You write the SQL and one line for each claim. `#sql_check` needs no proof: it
answers `false` with the rows, `proved`, or `unknown`. A fact about one
database is one line, `decide +kernel`. A claim about every database that the
check cannot prove needs a proof in Lean, and the intended author of that
proof is your coding agent. The [cheat sheet](cheat-sheet.md) has the lines
that you write.

## How long are the proofs?

For some claims, one line. For others, long: the proof that the table rebuild
of the README keeps the sessions has about 465 lines. An agent can write such
a proof, but it costs time, and it does not always finish. Shorter proofs of
the common claims are the main work that remains in the library. The table
[What an agent can finish today](guide/agents.md#what-an-agent-can-finish-today)
gives the cost of each kind of claim.

## What does a proof not cover?

A proof is about what the statements do to the data on one connection. It says
nothing about locks, query plans, speed, concurrent connections, crashes, I/O
errors or extensions. It also assumes the connection settings of the profile,
for example that foreign keys are off when the script starts unless you say
otherwise. The [assumptions](execution-profile.md#assumptions) are a complete
list.

## Will Belay accept my SQL?

Belay models a part of SQLite: tables with constraints, indexes, views,
triggers, `ALTER TABLE`, transactions, the data statements and most of
`SELECT`. SQL outside that part is refused with a reason when the file
compiles. Belay never approximates a statement that it does not model. Window
functions and attached databases are examples of SQL that it refuses today.
The [supported subset](semantic-subset.md) is the exact list.

## Which SQLite versions does it support?

One: SQLite 3.51.0. The cases are replayed against that release, so the
evidence is for that release. If your application uses a different release,
a proof tells you about your build only where the two releases agree.
[Execution profiles](execution-profile.md#sqlite-releases) say how to measure
the build that your application uses.

## Why SQLite first? When PostgreSQL?

SQLite is small enough to model one engine exactly, it has a large public test
suite, and it is in most applications and tools, also the ones that agents
write. The same method applies to other open-source engines, such as
PostgreSQL and ClickHouse. That work has no date: it needs funding. If you
want it for your database, write to contact@vihren.dev.

## Why Lean, and not an SMT solver?

The tools that decide SQL equivalence with a solver work on a general SQL
without the behavior of one engine: schema changes, errors, type affinity,
triggers. A migration bug is usually in that behavior. In Lean, the model can
follow one engine statement by statement, and the only part that you must
trust for a proof is Lean's kernel. Automation that is added later, a solver
also, has to produce a proof that the kernel checks, so it cannot make a false
claim pass. [Why trust it](../README.md#why-trust-it) states what a proof
rests on.

## How is Belay different from a query type-checker or a migration linter?

Those tools check that names and types agree with a schema, or they warn about
kinds of operations that are dangerous in general. They do not answer whether
this migration keeps the result of this query, or whether it succeeds on the
data that the schema allows. Belay answers those two questions, and you can
use it with such tools. [What you can state](../README.md#what-you-can-state)
lists the questions.

## What does it cost to install and build?

You need [elan](https://github.com/leanprover/elan) and git. You do not need a
C compiler or Nix. The first build takes some minutes, about seven on a
machine with eight cores, and later builds take seconds. CI builds and tests
the library on Linux (x86-64) and macOS (Apple silicon).
[Install](../README.md#install) has the steps.

## Is it ready for production?

Belay is at version 0.2.0. The model is pinned to one SQLite release and
checked on every change. The notation for claims is new and can change before
version 1.0, and a later version can ask you to state a claim in a different
form. A theorem that compiles with a version stays true for that version.
Use it today to find counterexamples and to prove the claims that matter most,
and keep your tests. [What an agent can finish today](guide/agents.md#what-an-agent-can-finish-today)
shows what is reliable now.

## Who makes Belay, and what is the license?

Tzanko Matev, as the project Vihren. The code has the MIT license. The project
looks for funding and for design partners who want formal verification for
their workloads on SQLite or other open-source databases: contact@vihren.dev.
The project accepts issues, reproductions and test cases, and does not accept
pull requests that change code; [CONTRIBUTING.md](../CONTRIBUTING.md) gives
the reason.
