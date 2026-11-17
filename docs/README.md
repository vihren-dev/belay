# Documentation

## Use Belay

These pages are for developers who use the library.

- [Questions and answers](faq.md): what a proof means, what Belay does not
  cover, and what it costs to use.
- [Cheat sheet](cheat-sheet.md): how to define SQL, load it from files, state
  a claim and check it.
- [Use Belay with a coding agent](guide/agents.md): the agent writes the
  proofs, and you state and review the claims.
- [Supported subset](semantic-subset.md): the SQL that the model handles, and
  the restrictions with their stable ids.
- [Execution profiles](execution-profile.md): the SQLite build and the
  connection settings for which a proof holds.

The [README](../README.md) has the installation steps and a first example. The
[surface library's README](../packages/belay/README.md) describes each claim.

## Development

These pages are for the people and the agents who work on the repository.
[CONTRIBUTING.md](../CONTRIBUTING.md) is the place to start.

| Folder | Contents | Does it describe the current state? |
| --- | --- | --- |
| [`development/`](development/) | How the repository works: CI, the review checklist, the conformance formats and tools, the parser boundary. | Yes. A page that is out of date says so below its title. |
| [`adr/`](adr/) | Design records. Each one gives a decision and its reasons. | A record gives its status. A later record can replace it. |
| [`records/`](records/) | Dated findings, inventories and requests. | No. A record is true for its date only. |
