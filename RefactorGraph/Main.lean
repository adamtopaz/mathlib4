import Lean

open Lean Std

def eprintln (s : String) : CoreM Unit := do
  IO.eprintln s

-- Build reverse dependency map: for each name, who directly depends on it
def buildReverseDeps : CoreM (HashMap Name NameSet) := do
  eprintln "Building reverse dependency map"
  let constants := (← getEnv).constants.toList
  let size := constants.length
  let mut out : HashMap Name NameSet := {}
  let mut counter := 0
  for (n, c) in constants do
    counter := counter + 1
    if counter % 10000 == 0 then
      eprintln s!"  {Nat.toFloat 100 * counter.toFloat / size.toFloat }%"
    for dep in c.getUsedConstantsAsSet do
      out := out.insert dep ((out[dep]?.getD {}).insert n)
  return out

-- Compute all constants that transitively depend on `nm` (including `nm` itself)
def transitiveDependents (nm : Name) (reverseDeps : HashMap Name NameSet) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut todo : Array Name := #[nm]
  while todo.size > 0 do
    let some current := todo.back? | break
    todo := todo.pop
    if !visited.contains current then
      visited := visited.insert current
      for dep in (reverseDeps[current]?.getD {}).toList do
        if !visited.contains dep then
          todo := todo.push dep
  return visited

def computeNodes (nm : Name) : CoreM NameSet := do
  eprintln "Computing nodes"
  let reverseDeps ← buildReverseDeps
  return transitiveDependents nm reverseDeps

-- Compute transitive dependencies, restricted to `restrict` set, using memoization cache
def transitiveDependenciesAux (env : Environment) (nm : Name) (restrict : NameSet)
    (cache : HashMap Name NameSet) : NameSet × HashMap Name NameSet :=
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
        -- Check if we have a cached result for this node
        if let some cached := cache[current]? then
          for d in cached.toList do
            visited := visited.insert d
        else
          visited := visited.insert current
          if let some ci := env.find? current then
            for dep in ci.getUsedConstantsAsSet do
              if restrict.contains dep && !visited.contains dep then
                todo := todo.push dep
    -- Cache the result for nm
    cache := cache.insert nm visited
    return (visited, cache)

def transitivelyClosedDAG (names : NameSet) : CoreM (HashMap Name NameSet) := do
  eprintln "Computing transitively closed DAG"
  let env ← getEnv
  let mut out : HashMap Name NameSet := {}
  let mut cache : HashMap Name NameSet := {}
  let mut counter := 0
  let size := names.size
  for a in names do
    counter := counter + 1
    if counter % 100 == 0 then
      eprintln s!"{Nat.toFloat 100 * counter.toFloat / size.toFloat }%"
    let (deps, newCache) := transitiveDependenciesAux env a names cache
    cache := newCache
    out := out.insert a deps
  return out

-- Leaves are nodes with no dependencies (other than themselves)
def leaves (tc : HashMap Name NameSet) : NameSet := Id.run do
  let mut out : NameSet := {}
  for (a, deps) in tc do
    -- A leaf has no dependencies other than itself
    if deps.toList.all (· == a) then
      out := out.insert a
  return out

-- Transitive reduction of `transitivelyClosedDAG names`
def reducedDAG (names : NameSet) : CoreM (HashMap Name NameSet) := do
  let tc ← transitivelyClosedDAG names
  eprintln "Computing reduced DAG"
  let mut out : HashMap Name NameSet := {}
  for a in names do
    let deps : NameSet := tc[a]?.getD {}
    let depsList := deps.toList.filter (· != a)  -- Compute once, exclude self
    let mut reduced : NameSet := {}
    for b in depsList do
      -- Check if b is reachable through some other dependency c
      let mut dominated := false
      for c in depsList do
        if c != b && (tc[c]?.getD {}).contains b then
          dominated := true
          break
      if !dominated then
        reduced := reduced.insert b
    out := out.insert a reduced
  return out

def entrypoint (nm : Name) : CoreM UInt32 := do
  let nodes ← computeNodes nm
  let dag ← reducedDAG nodes
  let leaves := leaves dag
  for leaf in leaves do
    println! leaf
  return 0

def main (args : List String) : IO UInt32 := do
  let [arg] := args | throw <| .userError s!"Expected a single argument, got {args.length}"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Mathlib }] {}
  Core.CoreM.toIO' (ctx := { fileName := "<INPUT>", fileMap := default }) (s := { env }) <|
    entrypoint arg.toName
