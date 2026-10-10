import LeanLinter

/-!
# The `lean-linter` command

`lean-linter [options] Module...` imports the modules, runs the checks on the declarations of the
target library, and prints one finding per line. See `usage` below and `README.md`.
-/

open Lean LeanLinter

def usage : String := s!"lean-linter {version}: find names, docstrings and declarations that
disagree with the code they describe.

usage: lean-linter [options] Module...

Imports the given modules and reports problems in the declarations of the target library, which
by default is every module under the first component of each module given (`Mathlib` for
`Mathlib.Order.Basic`). Run it with the project's search path: `lake exe lean-linter MyLib` in a
project that requires lean-linter, or `lake env path/to/lean-linter MyLib` in any other.

options:
  --checks a,b,...   run only these checks (see --list)
  --root Prefix      report on modules under Prefix (repeatable)
  --json             print findings as JSON lines instead of tab-separated text
  --list             list the checks and exit
  --version          print the version and exit
  -h, --help         print this message and exit

exit status: 0 if nothing was found, 1 if something was, 2 on a usage error."

/-- The parsed command line. -/
structure CliOptions where
  checks : Option (List String) := none
  roots : Array Name := #[]
  modules : Array Name := #[]
  json : Bool := false

/-- What the command line asks for: options to run with, or text to print and an exit code. -/
inductive Parsed where
  | run (opts : CliOptions)
  | exit (text : String) (code : UInt32)

def parseArgs : List String → CliOptions → Parsed
  | [], opts => .run opts
  | "--checks" :: cs :: rest, opts => parseArgs rest { opts with checks := some (cs.splitOn ",") }
  | "--root" :: p :: rest, opts => parseArgs rest { opts with roots := opts.roots.push p.toName }
  | "--json" :: rest, opts => parseArgs rest { opts with json := true }
  | "--list" :: _, _ =>
    .exit ("\n".intercalate (allChecks.map fun c => s!"{c.name}{"".pushn ' ' (20 - c.name.length)}{c.summary}")) 0
  | "--version" :: _, _ => .exit s!"lean-linter {version}" 0
  | "-h" :: _, _ | "--help" :: _, _ => .exit usage 0
  | arg :: rest, opts =>
    if arg.startsWith "-" then .exit s!"unknown or incomplete option `{arg}`\n\n{usage}" 2
    else parseArgs rest { opts with modules := opts.modules.push arg.toName }

/-- A finding as one line of tab-separated text: check, declaration, `Module:line`, message. -/
def LeanLinter.Finding.toText (f : Finding) : String :=
  s!"{f.check}\t{userName f.decl}\t{f.module}:{f.line}\t{f.message}"

/-- A finding as one line of JSON. -/
def LeanLinter.Finding.toJsonLine (f : Finding) : String :=
  Json.compress <| Json.mkObj [("check", f.check), ("declaration", toString (userName f.decl)),
    ("module", toString f.module), ("line", f.line), ("message", f.message)]

unsafe def main (args : List String) : IO UInt32 := do
  let opts ← match parseArgs args {} with
    | .exit text code => do (if code == 0 then IO.println text else IO.eprintln text); return code
    | .run opts => pure opts
  if opts.modules.isEmpty then
    IO.eprintln usage
    return 2
  let checks ← match opts.checks with
    | none => pure allChecks
    | some names =>
      match names.find? (fun n => !allChecks.any (·.name == n)) with
      | some bad => IO.eprintln s!"unknown check `{bad}`; `lean-linter --list` shows them"; return 2
      | none => pure (allChecks.filter (names.contains ·.name))
  initSearchPath (← findSysroot)
  -- Environment extensions (the instance table among them) are only filled in when their
  -- initializers run, which is what `loadExts` asks for.
  enableInitializersExecution
  let env ← importModules (opts.modules.map ({ module := · })) {} (trustLevel := 1024) (loadExts := true)
  let roots := if opts.roots.isEmpty then opts.modules.map (·.getRoot) else opts.roots
  let ctx := Ctx.build env roots
  IO.eprintln s!"lean-linter {version}: {ctx.decls.size} declarations under {roots.toList}"
  let mut total := 0
  for check in checks do
    let start ← IO.monoMsNow
    let findings ← check.run ctx
    let sorted := findings.qsort fun a b =>
      toString a.module < toString b.module || (a.module == b.module && a.line < b.line)
    for f in sorted do
      IO.println (if opts.json then f.toJsonLine else f.toText)
    IO.eprintln s!"{check.name}: {findings.size} ({(← IO.monoMsNow) - start} ms)"
    total := total + findings.size
  return if total == 0 then 0 else 1
