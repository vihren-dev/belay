/* Pure graph operations shared by the offline report and its executable tests. */
"use strict";

/** @typedef {{name:string, displayName?:string, module:string, kind:string,
 * private?:boolean, internal?:boolean, selection?:number[]|null,
 * typeReferences?:string[], bodyReferences?:string[], bodyAvailable?:boolean}} Declaration */
/** @typedef {{name:string, path:string[]}} Route */
/** @typedef {{nodes:Map<string, Declaration>, owned:Set<string>,
 * incoming:Map<string, {type:string[], body:string[]}>}} Graph */

/** Index all declarations, including private helpers and external boundary nodes. */
function dependencyGraph(data) {
  const nodes = new Map([...data.external, ...data.declarations].map(node => [node.name, node]));
  const owned = new Set(data.declarations.map(node => node.name));
  const incoming = new Map();
  for (const node of data.declarations) {
    for (const kind of ["type", "body"]) {
      for (const target of new Set(node[kind + "References"] || [])) {
        if (!incoming.has(target)) incoming.set(target, {type: [], body: []});
        incoming.get(target)[kind].push(node.name);
      }
    }
  }
  return {nodes, owned, incoming};
}

/** Get distinct direct neighbours for the selected direction and edge categories. */
function dependencyNeighbours(graph, name, direction, kinds) {
  const node = graph.nodes.get(name);
  const refs = graph.incoming.get(name);
  return [...new Set(kinds.flatMap(kind => direction === "incoming"
    ? refs?.[kind] || [] : node?.[kind + "References"] || []))].sort();
}

/** Return one shortest route per visible neighbour; helper cycles terminate. */
function dependencyRoutes(graph, start, direction, kinds, fold) {
  if (!fold) return dependencyNeighbours(graph, start, direction, kinds)
    .map(name => ({name, path: [start, name]}));
  const seen = new Set([start]);
  const queue = [{name: start, path: [start]}];
  const routes = [];
  for (let index = 0; index < queue.length; index++) {
    const current = queue[index];
    for (const name of dependencyNeighbours(graph, current.name, direction, kinds)) {
      if (seen.has(name)) continue;
      seen.add(name);
      const route = {name, path: [...current.path, name]};
      if (fold && graph.nodes.get(name)?.internal) queue.push(route);
      else routes.push(route);
    }
  }
  return routes.sort((left, right) => left.name.localeCompare(right.name));
}

/** Find a shortest dependency or user path without discarding helper nodes. */
function dependencyPath(graph, start, target, direction, kinds) {
  const parents = new Map([[start, null]]);
  const queue = [start];
  for (let index = 0; index < queue.length; index++) {
    const current = queue[index];
    if (current === target) {
      const path = [];
      for (let name = target; name !== null; name = parents.get(name)) path.push(name);
      return path.reverse();
    }
    for (const name of dependencyNeighbours(graph, current, direction, kinds)) {
      if (!parents.has(name)) { parents.set(name, current); queue.push(name); }
    }
  }
  return null;
}

/** Count project references between owning modules, separately for each category. */
function dependencyModules(graph, modules) {
  const rows = new Map(modules.map(module => [module.name,
    {name: module.name, declarations: 0, type: new Set(), body: new Set(), imports: module.imports || []}]));
  for (const name of graph.owned) {
    const node = graph.nodes.get(name), row = rows.get(node.module);
    if (!row) continue;
    row.declarations++;
    for (const kind of ["type", "body"]) {
      for (const target of node[kind + "References"] || []) {
        const other = graph.nodes.get(target);
        if (graph.owned.has(target) && other.module !== node.module) row[kind].add(other.module);
      }
    }
  }
  return [...rows.values()].map(row => ({...row, type: [...row.type].sort(), body: [...row.body].sort()}));
}

/** Find inspection candidates; these heuristics do not establish redundancy. */
function dependencyCandidates(graph) {
  const wrappers = [], frequent = [], unused = [], groups = new Map();
  for (const name of graph.owned) {
    const node = graph.nodes.get(name);
    if (node.kind !== "theorem" || node.internal) continue;
    const users = dependencyNeighbours(graph, name, "incoming", ["type", "body"]).filter(user => user !== name);
    if (!users.length) unused.push(name);
    frequent.push({name, count: users.length});
    const body = [...new Set(node.bodyReferences || [])].sort();
    const theoremRefs = body.filter(target => graph.nodes.get(target)?.kind === "theorem" && target !== name);
    if (theoremRefs.length === 1) wrappers.push({name, target: theoremRefs[0]});
    if (body.length) {
      const key = JSON.stringify(body);
      if (!groups.has(key)) groups.set(key, []);
      groups.get(key).push(name);
    }
  }
  frequent.sort((left, right) => right.count - left.count || left.name.localeCompare(right.name));
  const matching = [...groups.values()].filter(group => group.length > 1)
    .sort((left, right) => right.length - left.length || left[0].localeCompare(right[0]));
  return {wrappers, frequent, unused, matching};
}

if (typeof module !== "undefined") module.exports = {
  dependencyGraph, dependencyNeighbours, dependencyRoutes, dependencyPath, dependencyModules, dependencyCandidates
};
