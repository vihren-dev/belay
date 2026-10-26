/* Check the report's actual graph code on hidden helper paths and cycles. */
"use strict";
const assert = require("node:assert/strict");
const {dependencyGraph, dependencyNeighbours, dependencyRoutes, dependencyPath,
  dependencyModules, dependencyCandidates} = require("../tools/theorem_dependency_graph.js");

/** Make a declaration with distinct type and proof dependencies for the report fixture. */
function declaration(name, module, typeReferences, bodyReferences, internal = false, kind = "theorem") {
  return {name, module, typeReferences, bodyReferences, internal, kind, bodyAvailable: true};
}

const modules = [{name: "One", imports: ["Base"]}, {name: "Two", imports: ["One"]}, {name: "Orphan", imports: []}];
const graph = dependencyGraph({modules, declarations: [
  declaration("wrapper", "One", ["typeOnly"], ["helper"]),
  declaration("helper", "One", [], ["cycle", "helper"], true, "definition"),
  declaration("cycle", "One", [], ["helper", "leaf", "external"], true, "definition"),
  declaration("leaf", "Two", [], []),
  declaration("typeOnly", "Two", [], []),
  declaration("twin1", "One", [], ["leaf", "external", "external"]),
  declaration("twin2", "One", [], ["external", "leaf"]),
  declaration("unrelated", "Orphan", [], ["unrelated"]),
], external: [{name: "external", module: "Lean", kind: "definition"}]});

// Type filters cannot leak body references, and repeated references count once.
assert.deepEqual(dependencyNeighbours(graph, "wrapper", "outgoing", ["type"]), ["typeOnly"]);
assert.deepEqual(dependencyNeighbours(graph, "external", "incoming", ["body"]), ["cycle", "twin1", "twin2"]);
assert.deepEqual(dependencyRoutes(graph, "wrapper", "outgoing", ["body"], false), [
  {name: "helper", path: ["wrapper", "helper"]}
]);
assert.deepEqual(dependencyRoutes(graph, "helper", "outgoing", ["body"], false), [
  {name: "cycle", path: ["helper", "cycle"]},
  {name: "helper", path: ["helper", "helper"]}
]);
assert.deepEqual(dependencyRoutes(graph, "unrelated", "incoming", ["body"], false), [
  {name: "unrelated", path: ["unrelated", "unrelated"]}
]);
assert.deepEqual(dependencyRoutes(graph, "unrelated", "outgoing", ["body"], true), []);
assert.deepEqual(dependencyRoutes(graph, "wrapper", "outgoing", ["body"], true), [
  {name: "external", path: ["wrapper", "helper", "cycle", "external"]},
  {name: "leaf", path: ["wrapper", "helper", "cycle", "leaf"]}
]);
assert.deepEqual(dependencyRoutes(graph, "leaf", "incoming", ["body"], true), [
  {name: "twin1", path: ["leaf", "twin1"]},
  {name: "twin2", path: ["leaf", "twin2"]},
  {name: "wrapper", path: ["leaf", "cycle", "helper", "wrapper"]}
]);
assert.deepEqual(dependencyPath(graph, "wrapper", "leaf", "outgoing", ["body"]), ["wrapper", "helper", "cycle", "leaf"]);
assert.deepEqual(dependencyPath(graph, "leaf", "wrapper", "incoming", ["body"]), ["leaf", "cycle", "helper", "wrapper"]);
assert.equal(dependencyPath(graph, "wrapper", "leaf", "outgoing", ["type"]), null);
assert.equal(dependencyPath(graph, "helper", "unrelated", "outgoing", ["body"]), null);
assert.deepEqual(dependencyPath(graph, "helper", "helper", "outgoing", []), ["helper"]);
assert.deepEqual(dependencyModules(graph, modules), [
  {name: "One", declarations: 5, type: ["Two"], body: ["Two"], imports: ["Base"]},
  {name: "Two", declarations: 2, type: [], body: [], imports: ["One"]},
  {name: "Orphan", declarations: 1, type: [], body: [], imports: []}
]);
const candidates = dependencyCandidates(graph);
assert.deepEqual(candidates.wrappers, [{name: "twin1", target: "leaf"}, {name: "twin2", target: "leaf"}]);
assert.deepEqual(candidates.matching, [["twin1", "twin2"]]);
assert.deepEqual(candidates.frequent[0], {name: "leaf", count: 3});
assert.deepEqual(candidates.unused, ["wrapper", "twin1", "twin2", "unrelated"]);
assert.equal(graph.nodes.size, 9); // Folding leaves all raw nodes intact.
console.log("Dependency report graph checks passed.");
