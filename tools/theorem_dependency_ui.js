/* Focused declaration navigation. All exported text enters the DOM as text. */
"use strict";
const data = JSON.parse(document.getElementById("graph-data").textContent);
const graph = dependencyGraph(data);
const moduleData = new Map(data.modules.map(item => [item.name, item]));
const proofCosts = new Map((data.proofCosts || []).map(item => [item.name, item]));
const searchOrder = [...data.declarations].sort((left, right) =>
  Number(left.internal || left.kind !== "theorem") - Number(right.internal || right.kind !== "theorem")
  || left.name.localeCompare(right.name));
let selected = null, searchLimit = 80, routeLimit = 100;

/** Find a fixed report control. */
function control(id) { return document.getElementById(id); }

/** Create an element with text, never interpreted markup. */
function element(tag, text = "", className = "") {
  const item = document.createElement(tag);
  item.textContent = text;
  item.className = className;
  return item;
}

/** Link a displayed name to the exact declaration, including private names. */
function declarationButton(name) {
  const node = graph.nodes.get(name);
  const button = element("button", node?.displayName || name, "declaration");
  button.title = name;
  button.onclick = () => selectDeclaration(name);
  return button;
}

/** Read the chosen edge categories without changing the underlying graph. */
function edgeKinds() {
  return ["type", "body"].filter(kind => control(kind + "-edges").checked);
}

/** Search both names and a selected owning module, with bounded DOM output. */
function renderSearch() {
  const query = control("search").value.trim().toLocaleLowerCase();
  const module = control("module-filter").value;
  const matches = searchOrder.filter(node => (!module || node.module === module) &&
    (node.name.toLocaleLowerCase().includes(query) || (node.displayName || "").toLocaleLowerCase().includes(query)));
  control("matches").replaceChildren(...matches.slice(0, searchLimit).map(node => declarationButton(node.name)));
  control("search-count").textContent = `${matches.length.toLocaleString()} matches; showing ${Math.min(matches.length, searchLimit)}.`;
  control("more-search").hidden = matches.length <= searchLimit;
}

/** Render a path with selectable intermediate helpers. */
function pathList(path) {
  const list = element("ol", "", "path");
  for (const name of path) {
    const item = element("li");
    item.append(declarationButton(name));
    list.append(item);
  }
  return list;
}

/** Show direct or folded edges without labelling a folded path as a direct edge. */
function renderRoutes() {
  if (!selected) return;
  const direction = control("direction").value, kinds = edgeKinds();
  const routes = dependencyRoutes(graph, selected, direction, kinds, control("fold").checked);
  const rows = routes.slice(0, routeLimit).map(route => {
    const row = element("div", "", "route");
    row.append(declarationButton(route.name));
    if (route.path.length > 2) {
      const details = element("details");
      details.append(element("summary", `Folded path · ${route.path.length - 2} internal helpers`), pathList(route.path));
      row.append(details);
    } else {
      const owner = direction === "outgoing" ? selected : route.name;
      const target = direction === "outgoing" ? route.name : selected;
      const categories = kinds.filter(kind => (graph.nodes.get(owner)?.[kind + "References"] || []).includes(target));
      row.append(element("span", "Direct · " + categories.join(" + "), "tag"));
    }
    return row;
  });
  control("routes").replaceChildren(...rows);
  control("route-count").textContent = `${routes.length.toLocaleString()} ${direction === "outgoing" ? "dependencies" : "users"}; showing ${rows.length}.`;
  control("more-routes").hidden = routes.length <= routeLimit;
  control("path-result").replaceChildren();
}

/** Show source context from the exported source snapshot, with one-based line numbers. */
function renderSource(node) {
  const module = moduleData.get(node.module);
  control("source-text").replaceChildren();
  if (!module?.sourceText || !node.selection) {
    control("source-location").textContent = "Source context is unavailable for this declaration.";
    return;
  }
  const [start, column, end] = node.selection, lines = module.sourceText.split("\n");
  control("source-location").textContent = `${module.source}:${start + 1}:${column + 1} · exported source snapshot`;
  for (let index = Math.max(0, start - 5); index < Math.min(lines.length, end + 16); index++) {
    control("source-text").append(element("span", `${index + 1}  ${lines[index]}`,
      "source-line" + (index >= start && index <= end ? " selected-line" : "")));
  }
}

/** Select a declaration and keep its exact name in the URL fragment for sharing. */
function selectDeclaration(name) {
  const node = graph.nodes.get(name);
  if (!node) return;
  selected = name; routeLimit = 100;
  control("selected-title").textContent = node.displayName || name;
  const flags = [node.kind, node.private ? "private" : "", node.internal ? "internal" : "",
    graph.owned.has(name) ? "project" : "external", node.bodyAvailable === false ? "body unavailable" : ""].filter(Boolean);
  control("metadata").textContent = `${name}\n${node.module} · ${flags.join(" · ")}`;
  const cost = proofCosts.get(name);
  control("cost").textContent = cost ? "Supplied proof cost: " + JSON.stringify(cost) : "Proof cost: no measurement supplied.";
  renderSource(node); renderRoutes();
  history.replaceState(null, "", "#" + encodeURIComponent(name));
}

/** Display a shortest route under the selected direction and edge filters. */
function findPath() {
  const target = control("target").value.trim();
  const output = control("path-result");
  if (!selected) return;
  if (!graph.nodes.has(target)) { output.textContent = "Unknown kernel name. Select a declaration to inspect its exact name."; return; }
  const path = dependencyPath(graph, selected, target, control("direction").value, edgeKinds());
  output.replaceChildren(path ? pathList(path) : element("p", "No path under the selected direction and edge categories."));
}

control("summary").textContent = `${data.declarations.length.toLocaleString()} project declarations · ${data.modules.length} selected modules · Lean ${data.leanVersion}.`;
control("coverage").textContent = JSON.stringify({coverage: data.coverage || "No coverage manifest supplied",
  provenance: data.provenance || "No provenance supplied", proofCostCoverage: data.proofCostCoverage || "No proof-cost manifest supplied",
  modules: data.modules.map(({sourceText, ...metadata}) => metadata)}, null, 2);
for (const module of data.modules) {
  const option = element("option", module.name); option.value = module.name; control("module-filter").append(option);
}
for (const id of ["search", "module-filter"]) control(id).oninput = () => { searchLimit = 80; renderSearch(); };
for (const id of ["direction", "type-edges", "body-edges", "fold"]) control(id).onchange = () => { routeLimit = 100; renderRoutes(); };
control("more-search").onclick = () => { searchLimit += 200; renderSearch(); };
control("more-routes").onclick = () => { routeLimit += 200; renderRoutes(); };
control("find-path").onclick = findPath;
control("target").onkeydown = event => { if (event.key === "Enter") findPath(); };
renderSearch();
let initial = null;
try { initial = decodeURIComponent(location.hash.slice(1)); } catch { /* A malformed fragment does not block browsing. */ }
selectDeclaration(graph.nodes.has(initial) ? initial : searchOrder.find(node => node.name.endsWith("runSqlFrom_notNull"))?.name || searchOrder[0]?.name);
