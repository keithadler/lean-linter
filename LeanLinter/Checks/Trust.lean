import LeanLinter.Basic

/-!
# `trust`: what a formalization asks you to believe besides Lean's kernel

Lean's kernel guarantees that every proof is correct *relative to its axioms*. A project can widen
what you have to trust in a handful of ways, and each leaves a mark that this check lists:

* `sorry`: the declaration is unproved.
* a user `axiom`: assumed, not proved.
* `native_decide`: the proof rests on an axiom saying compiled code computes the right answer
  (`Lean.ofReduceBool`, or in newer Lean a `_native` axiom per use), so on compiled code being
  right and not only on the kernel.
* `unsafe`, `implemented_by`, `extern`: code the kernel does not see; unsound code here can make
  `native_decide` prove falsehoods.
* an `opaque` constant: an arbitrary value, with only its type known.

Each finding is about the declaration itself (what it contains directly), not about everything it
depends on; for that, see the theorem report card (`--card`). A library that is clean here, as
Mathlib is, has nothing to list. A project in progress, like FLT, lists its to-do list.
-/

open Lean

namespace LeanLinter

def trust (ctx : Ctx) : IO (Array Finding) := do
  let mut out := #[]
  for d in ctx.decls do
    if ctx.isDeprecated d.name then continue
    match d.info with
    | .axiomInfo _ => out := out.push <| ctx.finding "trust" d "an axiom: assumed, not proved"
    | .opaqueInfo _ =>
      out := out.push <| ctx.finding "trust" d "an `opaque` constant: only its type is known"
    | _ => pure ()
    if d.info.isUnsafe then
      out := out.push <| ctx.finding "trust" d "`unsafe`: the kernel does not check it"
    if let some v := d.info.value? (allowOpaque := true) then
      let used := usedConstants v
      if used.contains ``sorryAx then
        out := out.push <| ctx.finding "trust" d "contains `sorry`"
      -- older Lean uses the axiom `Lean.ofReduceBool`; newer Lean declares one axiom per use,
      -- under a `_native` name
      let native := used.any fun u =>
        u == `Lean.ofReduceBool
          || (u.components.any (· == `_native) && (ctx.env.find? u).any (·.isAxiom))
      if native then
        out := out.push <| ctx.finding "trust" d
          "uses `native_decide`: rests on compiled code being correct, not only on the kernel"
    if (Compiler.getImplementedBy? ctx.env d.name).isSome then
      out := out.push <| ctx.finding "trust" d "has an `implemented_by`: compiled code differs from the definition"
    if isExtern ctx.env d.name then
      out := out.push <| ctx.finding "trust" d "is `extern`: implemented in native code"
  return out

def trustCheck : Check where
  name := "trust"
  summary := "sorry, axiom, native_decide, unsafe, implemented_by, extern, opaque"
  run := trust

end LeanLinter
