import Lean

open Lean Std

def computeNodes (nm : Name) : CoreM NameSet := do
  println! "Computing nodes"
  let mut out : NameSet := {}
  for (n, c) in (← getEnv).constants do
    if c.getUsedConstantsAsSet.contains nm then out := out.insert n
  return out.insert nm

def transitiveDependencies (nm : Name) : CoreM NameSet := do
  let env ← getEnv
  let mut visited : NameSet := {}
  let mut todo : Array Name := #[nm]
  while todo.size > 0 do
    let some current := todo.back? | break
    todo := todo.pop
    if !visited.contains current then
      visited := visited.insert current
      if let some ci := env.find? current then
        for dep in ci.getUsedConstantsAsSet do
          if !visited.contains dep then
            todo := todo.push dep
  return visited

def transitivelyClosedDAG (names : NameSet) : CoreM (HashMap Name NameSet) := do
  println! "Computing transitively closed DAG"
  let mut out := {}
  let mut counter := 0
  let size := names.size
  for a in names do
    counter := counter + 1
    println! s!"{Nat.toFloat 100 * counter.toFloat / size.toFloat }"
    out := out.insert a <| (← transitiveDependencies a).filter names.contains
  return out

-- Transitive reduction of `transitivelyClosedDAG names`
def reducedDAG (names : NameSet) : CoreM (HashMap Name NameSet) := do
  let tc ← transitivelyClosedDAG names
  println! "Computing reduced DAG"
  let mut out : HashMap Name NameSet := {}
  for a in names do
    let deps : NameSet := tc[a]?.getD {}
    let mut reduced : NameSet := {}
    for b in deps.toList do
      if b == a then continue  -- Skip self
      -- Check if b is reachable through some other dependency c
      let mut dominated := false
      for c in deps.toList do
        if c != b && c != a && (tc[c]?.getD {}).contains b then
          dominated := true
          break
      if !dominated then
        reduced := reduced.insert b
    out := out.insert a reduced
  return out

def entrypoint (nm : Name) : CoreM UInt32 := do
  let nodes ← computeNodes nm
  let dag ← reducedDAG nodes
  for (a,s) in dag do for b in s do
    println! s!"{a} --> {b}"
  return 0

def main (args : List String) : IO UInt32 := do
  let [arg] := args | throw <| .userError s!"Expected a single argument, got {args.length}"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Mathlib }] {}
  Core.CoreM.toIO' (ctx := { fileName := "<INPUT>", fileMap := default }) (s := { env }) <|
    entrypoint arg.toName
