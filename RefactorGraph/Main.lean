import Lean
import Mathlib.Lean.Expr.Basic

open Lean Std

/-!
# Refactor Graph

Given a constant name `nm`, we compute:
1. `nodes`: all constants that transitively depend on `nm` (including `nm`)
2. `transitiveDeps`: for each node k, the transitive dependencies of k (restricted to nodes)
3. `directDependents`: for each node k, constants that directly depend on k (restricted to nodes)
-/

structure RefactorData where
  /-- All constants that transitively depend on the root (including the root itself) -/
  nodes : NameSet
  /-- For each node k, the set of transitive dependencies of k (restricted to nodes) -/
  transitiveDeps : HashMap Name NameSet
  /-- For each node k, the set of constants that directly depend on k (restricted to nodes) -/
  directDependents : HashMap Name NameSet

def eprintln (s : String) : CoreM Unit := IO.eprintln s

/-- Compute transitive dependencies of `nm` restricted to `restrict`, using memoization. -/
def transitiveDepsWithCache (forwardDeps : HashMap Name NameSet) (nm : Name)
    (restrict : NameSet) (cache : HashMap Name NameSet) : NameSet × HashMap Name NameSet :=
  if let some cached := cache[nm]? then
    (cached, cache)
  else Id.run do
    let mut visited : NameSet := {}
    let mut todo : Array Name := #[nm]
    let mut cache := cache
    while todo.size > 0 do
      let some current := todo.back? | break
      todo := todo.pop
      if !visited.contains current then
        -- Check cache for this node
        if let some cached := cache[current]? then
          for d in cached.toList do
            visited := visited.insert d
        else
          visited := visited.insert current
          for dep in (forwardDeps[current]?.getD {}).toList do
            if restrict.contains dep && !visited.contains dep then
              todo := todo.push dep
    cache := cache.insert nm visited
    return (visited, cache)

/-- Compute all refactor data for constant `nm` in a single efficient pass. -/
def computeRefactorData (nm : Name) : CoreM RefactorData := do
  let env ← getEnv
  let constants := env.constants.toList
  let numConstants := constants.length

  -------------------------------------------------
  -- Pass 1: Build forward and reverse dependency maps (single scan of all constants)
  -------------------------------------------------
  eprintln "Pass 1/3: Building dependency maps..."
  let mut forwardDeps : HashMap Name NameSet := {}
  let mut reverseDeps : HashMap Name NameSet := {}
  let mut counter := 0
  for (n, c) in constants do
    counter := counter + 1
    if counter % 10000 == 0 then
      eprintln s!"  {100.0 * counter.toFloat / numConstants.toFloat}%"
    -- Skip blacklisted names
    if ← n.isBlackListed then continue
    -- Filter out blacklisted dependencies
    let mut deps : NameSet := {}
    for dep in c.getUsedConstantsAsSet do
      if !(← dep.isBlackListed) then
        deps := deps.insert dep
    forwardDeps := forwardDeps.insert n deps
    for dep in deps do
      reverseDeps := reverseDeps.insert dep ((reverseDeps[dep]?.getD {}).insert n)
  eprintln s!"  Scanned {numConstants} constants"

  -------------------------------------------------
  -- Pass 2: Find all transitive dependents of nm (BFS on reverse graph)
  -------------------------------------------------
  eprintln "Pass 2/3: Finding transitive dependents..."
  let mut nodes : NameSet := {}
  let mut todo : Array Name := #[nm]
  while todo.size > 0 do
    let some current := todo.back? | break
    todo := todo.pop
    if !nodes.contains current then
      nodes := nodes.insert current
      for dependent in (reverseDeps[current]?.getD {}).toList do
        if !nodes.contains dependent then
          todo := todo.push dependent
  eprintln s!"  Found {nodes.size} nodes"

  -------------------------------------------------
  -- Pass 3: Compute transitiveDeps and directDependents for each node
  -------------------------------------------------
  eprintln "Pass 3/3: Computing transitive deps and direct dependents..."
  let mut transitiveDeps : HashMap Name NameSet := {}
  let mut directDependents : HashMap Name NameSet := {}
  let mut cache : HashMap Name NameSet := {}
  counter := 0
  let numNodes := nodes.size
  for k in nodes do
    counter := counter + 1
    if counter % 100 == 0 then
      eprintln s!"  {100.0 * counter.toFloat / numNodes.toFloat}%"
    -- Compute transitive dependencies of k (restricted to nodes)
    let (deps, newCache) := transitiveDepsWithCache forwardDeps k nodes cache
    cache := newCache
    transitiveDeps := transitiveDeps.insert k deps
    -- Compute direct dependents of k (restricted to nodes)
    let allDirectDependents := reverseDeps[k]?.getD {}
    directDependents := directDependents.insert k (allDirectDependents.filter nodes.contains)
  eprintln "  Done"

  return { nodes, transitiveDeps, directDependents }

-------------------------------------------------
-- Utility functions that operate on RefactorData
-------------------------------------------------

/-- Leaves are nodes with no dependencies other than themselves. -/
def RefactorData.leaves (data : RefactorData) : NameSet := Id.run do
  let mut out : NameSet := {}
  for (a, deps) in data.transitiveDeps do
    if deps.toList.all (· == a) then
      out := out.insert a
  return out

/-- Roots are nodes with no dependents (nothing depends on them within the node set). -/
def RefactorData.roots (data : RefactorData) : NameSet := Id.run do
  let mut out : NameSet := {}
  for (a, dependents) in data.directDependents do
    if dependents.isEmpty then
      out := out.insert a
  return out

/-- For each node k, the set of nodes that k directly depends on (restricted to nodes).
    This is the inverse of `directDependents`. -/
def RefactorData.directDependencies (data : RefactorData) : HashMap Name NameSet := Id.run do
  let mut out : HashMap Name NameSet := {}
  -- Initialize all nodes with empty sets
  for k in data.nodes do
    out := out.insert k {}
  -- If a ∈ directDependents[b], then b ∈ directDependencies[a]
  for (b, dependents) in data.directDependents do
    for a in dependents do
      out := out.insert a ((out[a]?.getD {}).insert b)
  return out

/-- For each node k, the set of nodes that transitively depend on k (restricted to nodes).
    This is the transitive closure of `directDependents`. -/
def RefactorData.transitiveDependents (data : RefactorData) : HashMap Name NameSet := Id.run do
  let mut out : HashMap Name NameSet := {}
  for k in data.nodes do
    -- BFS/DFS to find all transitive dependents of k
    let mut visited : NameSet := {}
    let mut todo : Array Name := #[k]
    while todo.size > 0 do
      let some current := todo.back? | break
      todo := todo.pop
      if !visited.contains current then
        visited := visited.insert current
        for dependent in (data.directDependents[current]?.getD {}).toList do
          if !visited.contains dependent then
            todo := todo.push dependent
    out := out.insert k visited
  return out

/-- Compute the transitive reduction (minimal edge set preserving reachability). -/
def RefactorData.reducedDAG (data : RefactorData) : HashMap Name NameSet := Id.run do
  let mut out : HashMap Name NameSet := {}
  for a in data.nodes do
    let deps := data.transitiveDeps[a]?.getD {}
    let depsList := deps.toList.filter (· != a)
    let mut reduced : NameSet := {}
    for b in depsList do
      -- Keep b if no other dep c has b in its transitive closure
      let mut dominated := false
      for c in depsList do
        if c != b && (data.transitiveDeps[c]?.getD {}).contains b then
          dominated := true
          break
      if !dominated then
        reduced := reduced.insert b
    out := out.insert a reduced
  return out

/-- Output the reduced DAG in DOT format. -/
def RefactorData.toDot (data : RefactorData) : String := Id.run do
  let reduced := data.reducedDAG
  let mut lines : Array String := #["digraph {"]
  for (a, deps) in reduced do
    for b in deps do
      lines := lines.push s!"  \"{a}\" -> \"{b}\""
  lines := lines.push "}"
  return "\n".intercalate lines.toList

/-- Compute equivalence classes of leaves of the restricted graph G.
    G has nodes = directDependents[nm] and edges from transitiveDeps restricted to G.
    Two leaves l1, l2 are equivalent iff some constant depends on both. -/
def RefactorData.leafEquivalenceClasses (data : RefactorData) (nm : Name) : Array (Array Name) := Id.run do
  -- Get nodes of G = directDependents[nm]
  let gNodes := data.directDependents[nm]?.getD {}

  -- Compute leaves of G (nodes with no dependencies within gNodes, other than self)
  let mut leavesArr : Array Name := #[]
  for k in gNodes.toList do
    let depsInG := (data.transitiveDeps[k]?.getD {}).filter fun d => gNodes.contains d && d != k
    if depsInG.isEmpty then
      leavesArr := leavesArr.push k

  if leavesArr.isEmpty then return #[]

  let n := leavesArr.size

  -- Build leaf name -> index map
  let mut leafIndex : HashMap Name Nat := {}
  for h : i in [:n] do
    leafIndex := leafIndex.insert leavesArr[i] i

  -- Union-Find: parent array where parent[i] = i initially
  let mut parent : Array Nat := Array.range n

  -- For each node a in data.nodes, union all leaves that a depends on
  for a in data.nodes.toList do
    let deps := data.transitiveDeps[a]?.getD {}
    -- Find indices of leaves that a depends on
    let mut indices : Array Nat := #[]
    for h : i in [:n] do
      if deps.contains leavesArr[i] then
        indices := indices.push i
    -- Union all to the same root
    if indices.size > 1 then
      -- Find root of first index
      let mut root := indices[0]!
      while parent[root]! != root do
        root := parent[root]!
      -- Union rest to this root
      for idx in indices do
        let mut r := idx
        while parent[r]! != r do
          r := parent[r]!
        if r != root then
          parent := parent.set! r root

  -- Collect equivalence classes by root
  let mut classMap : HashMap Nat (Array Name) := {}
  for h : i in [:n] do
    let mut root := i
    while parent[root]! != root do
      root := parent[root]!
    classMap := classMap.insert root ((classMap[root]?.getD #[]).push leavesArr[i])

  return (classMap.toList.map (·.2)).toArray

-------------------------------------------------
-- Main entry point
-------------------------------------------------

def entrypoint (nm : Name) : CoreM UInt32 := do
  let data ← computeRefactorData nm
  eprintln s!"Nodes: {data.nodes.size}"
  eprintln s!"Leaves: {data.leaves.size}"
  eprintln s!"Roots: {data.roots.size}"

  -- Compute and print leaf equivalence classes
  let classes := data.leafEquivalenceClasses nm
  eprintln s!"Leaf equivalence classes in directDependents[{nm}]: {classes.size}"
  IO.println s!"# Leaf equivalence classes ({classes.size} classes)"
  for h : i in [:classes.size] do
    let cls := classes[i]
    IO.println s!"\n## Class {i + 1} ({cls.size} leaves)"
    for leaf in cls do
      IO.println s!"  {leaf}"
  return 0

def main (args : List String) : IO UInt32 := do
  let [arg] := args | throw <| .userError s!"Expected a single argument, got {args.length}"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Mathlib }] {}
  Core.CoreM.toIO' (ctx := { fileName := "<INPUT>", fileMap := default }) (s := { env }) <|
    entrypoint arg.toName
