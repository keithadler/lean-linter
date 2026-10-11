import Lean

/-!
# Running `MetaM` from the command line

Checks that need unification or pretty-printing (`Meta.isDefEq`, `ppExpr`) run in `MetaM`. The
linter has an `Environment` and nothing else, so this builds the context `MetaM` needs.
-/

open Lean Meta

namespace LeanLinter

/-- Run `x` in `MetaM` over `env`, with a fresh local context and the given heartbeat budget
(in thousands, as `maxHeartbeats` is). A failure or a timeout comes back as an exception. -/
def runMeta (env : Environment) (x : MetaM α) (maxHeartbeats : Nat := 400000) : IO α := do
  let ctx : Core.Context := { fileName := "<lean-linter>", fileMap := default, maxHeartbeats }
  let (a, _) ← (x.run' {} {}).toIO ctx { env }
  return a

/-- `x`, or `none` if it threw (a timeout, usually). -/
def tryMeta (env : Environment) (x : MetaM α) : IO (Option α) := do
  try return some (← runMeta env x) catch _ => return none

end LeanLinter
