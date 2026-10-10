import LeanLinter

open Lean LeanLinter

def usage : String := "usage: lean-linter [--checks a,b,...] [--root Prefix]... Module...

Imports the given modules and reports problems in the declarations of the target library (by
default, every module under the first component of each module given). Run it with the project's
search path, e.g. `lake env lean-linter Mathlib` from the project's directory.

checks: " ++ ", ".intercalate (allChecks.map (·.1))

unsafe def main (args : List String) : IO UInt32 := do
  let mut checks : Option (List String) := none
  let mut roots : Array Name := #[]
  let mut mods : Array Name := #[]
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--checks" :: cs :: r => checks := some (cs.splitOn ","); rest := r
    | "--root" :: p :: r => roots := roots.push p.toName; rest := r
    | "-h" :: _ => IO.println usage; return 0
    | "--help" :: _ => IO.println usage; return 0
    | m :: r => mods := mods.push m.toName; rest := r
    | [] => rest := []
  if mods.isEmpty then
    IO.eprintln usage
    return 2
  let selected : List (String × (Ctx → IO (Array Finding))) := match checks with
    | some cs => allChecks.filter (fun c => cs.contains c.1)
    | none => allChecks
  if let some cs := checks then
    for c in cs do
      unless allChecks.any (fun x => x.1 == c) do
        IO.eprintln s!"unknown check `{c}`\n\n{usage}"
        return 2
  initSearchPath (← findSysroot)
  -- environment extensions (instances, among others) are only populated when their initializers run
  enableInitializersExecution
  let env ← importModules (mods.map ({ module := · })) {} (trustLevel := 1024) (loadExts := true)
  let targets := if roots.isEmpty then mods.map (·.getRoot) else roots
  let ctx ← Ctx.build env targets
  IO.eprintln s!"{ctx.decls.size} declarations in {targets.toList}"
  let mut total := 0
  for (name, run) in selected do
    let start ← IO.monoMsNow
    let fs ← run ctx
    for f in fs.qsort (fun a b => toString a.module < toString b.module || (a.module == b.module && a.line < b.line)) do
      IO.println s!"{f.check}\t{userName f.decl}\t{f.module}:{f.line}\t{f.message}"
    IO.eprintln s!"{name}: {fs.size} ({(← IO.monoMsNow) - start} ms)"
    total := total + fs.size
  return if total == 0 then 0 else 1
