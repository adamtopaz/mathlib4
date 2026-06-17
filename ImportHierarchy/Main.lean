module

import Lean
import ImportGraph.Imports

open Lean Std

/-- Helper for transitiveClosure: compute all reachable nodes from a given node -/
partial def transitiveClosureFrom (graph : HashMap Name (HashSet Name)) (node : Name) :
    MonadCacheT Name (HashSet Name) IO (HashSet Name) :=
  checkCache node fun _ => do
    let direct := graph[node]?.getD {}
    let mut result := direct
    for n in direct do
      let transitive ← transitiveClosureFrom graph n
      result := result.insertMany transitive
    return result

/-- Compute the transitive reduction of a transitively closed graph. -/
def transitiveReduction (tc : HashMap Name (HashSet Name)) :
    (HashMap Name (HashSet Name)) := Id.run do
  let mut result : HashMap Name (HashSet Name) := {}
  for (node, parents) in tc do
    let mut reduced := parents
    for p in parents do
      let pReachable := tc[p]?.getD {}
      for other in parents do
        if other != p && pReachable.contains other then
          reduced := reduced.erase other
    result := result.insert node reduced
  return result

/-- Convert a graph to Mermaid format for visualization.
    Arrow `a --> b` means `a` is a (reduced) transitive import of `b`. -/
def toMermaid (graph : HashMap Name (HashSet Name)) : String := Id.run do
  let mut lines : Array String := #["flowchart TD"]
  let mut nodesWithEdges : HashSet Name := {}
  for (node, imports) in graph do
    for imp in imports do
      lines := lines.push s!"  {imp} --> {node}"
      nodesWithEdges := nodesWithEdges.insert node
      nodesWithEdges := nodesWithEdges.insert imp
  -- Add isolated nodes (nodes with no edges)
  for (node, _) in graph do
    if !nodesWithEdges.contains node then
      lines := lines.push s!"  {node}"
  return "\n".intercalate lines.toList

public def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← Lean.importModules #[{ module := `Mathlib }] {}
  let modules := env.header.moduleNames
  let mut fullHierarchy : HashMap Name (HashSet Name) := {}
  for module in modules do
    let imports := env.importsOf module
    fullHierarchy := fullHierarchy.insert module (Std.HashSet.ofArray imports)
  let selection : HashSet Name := .ofList <| args.filterMap fun s =>
    if modules.contains s.toName then s.toName else none
  let fullRestrictedHierarchy : HashMap Name (HashSet Name) ←
    (computeRestrictedHierarchy fullHierarchy selection).run
  let restrictedHierarchy := transitiveReduction fullRestrictedHierarchy
  println! toMermaid restrictedHierarchy
  return 0
where computeRestrictedHierarchy
    (fullHierarchy : HashMap Name (HashSet Name))
    (selection : HashSet Name) :
    MonadCacheT Name (HashSet Name) IO (HashMap Name (HashSet Name)) := do
  let mut result : HashMap Name (HashSet Name) := {}
  for node in selection do
    let transitiveImports := (← transitiveClosureFrom fullHierarchy node).filter
      fun n => selection.contains n
    result := result.insert node transitiveImports
  return result
