/* Lazy overview panels keep the first declaration usable before analyses run. */
"use strict";

/** Render project module edges and keep imports distinct from proof references. */
function renderModules() {
  const target = control("modules");
  if (target.childElementCount) return;
  for (const row of dependencyModules(graph, data.modules)) {
    const details = element("details");
    details.append(element("summary", `${row.name} · ${row.declarations} declarations`));
    for (const [label, values] of [["Type reference targets", row.type], ["Proof/value targets", row.body], ["Imports", row.imports]]) {
      details.append(element("p", label + ": " + (values.join(", ") || "none")));
    }
    target.append(details);
  }
}

/** Bound a candidate list's initial DOM size without dropping its data. */
function candidateSection(title, explanation, items, render) {
  const details = element("details"), list = element("div", "", "candidate-list");
  details.append(element("summary", `${title} · ${items.length}`), element("p", explanation), list);
  let shown = 0;
  const more = element("button", "Show more candidates");
  const append = () => {
    for (const item of items.slice(shown, shown + 100)) list.append(render(item));
    shown += 100; more.hidden = shown >= items.length;
  };
  details.ontoggle = () => { if (details.open && !shown) append(); };
  more.onclick = append; details.append(more);
  return details;
}

/** Label theorem-family heuristics precisely so candidates remain reviewable. */
function renderCandidates() {
  const target = control("candidates");
  if (target.childElementCount) return;
  const candidates = dependencyCandidates(graph);
  target.append(candidateSection("Wrapper candidates", "Non-internal theorems with exactly one distinct direct theorem reference in their body. Other constants can still occur.",
    candidates.wrappers, item => {
      const row = element("div", "", "route");
      row.append(declarationButton(item.name), element("span", " → "), declarationButton(item.target)); return row;
    }));
  target.append(candidateSection("Frequently referenced theorems", "Distinct project consumers in types or bodies, excluding self references. Internal theorem targets are omitted from this view.",
    candidates.frequent.filter(item => item.count > 0), item => {
      const row = element("div", "", "route");
      row.append(declarationButton(item.name), element("span", `${item.count} consumers`, "tag")); return row;
    }));
  target.append(candidateSection("No project consumers", "Non-internal theorems with no other project declaration referencing them. External users and declarations outside the selected scope are unknown.",
    candidates.unused, name => { const row = element("div"); row.append(declarationButton(name)); return row; }));
  target.append(candidateSection("Matching body-reference neighbourhoods", "Non-internal theorems with identical, nonempty sets of direct body references. Equal dependencies do not imply equal statements or proofs.",
    candidates.matching, names => {
      const row = element("details");
      row.append(element("summary", `${names.length} theorems`), pathList(names)); return row;
    }));
}

control("module-view").ontoggle = () => { if (control("module-view").open) renderModules(); };
control("candidate-view").ontoggle = () => { if (control("candidate-view").open) renderCandidates(); };
