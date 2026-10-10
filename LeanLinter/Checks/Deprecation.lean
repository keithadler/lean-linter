import LeanLinter.Basic

/-!
# `deprecation`: a deprecation that leads nowhere, or to another deprecation

`@[deprecated new (since := ...)]` tells users to switch to `new`. That hint fails when `new`
does not exist, or is itself deprecated: following it lands on a second warning. In Mathlib, every
`Ideal.inertiaDeg_*` lemma points to an `inertiaDeg'_*` lemma that was deprecated in turn.
-/

open Lean

namespace LeanLinter

def deprecation (ctx : Ctx) : IO (Array Finding) := do
  let mut out := #[]
  for d in ctx.decls do
    let some entry := Linter.deprecatedAttr.getParam? ctx.env d.name | continue
    let some new := entry.newName? | continue
    if !ctx.env.contains new then
      out := out.push <| ctx.finding "deprecation" d
        s!"deprecated in favor of `{new}`, which does not exist"
    else if ctx.isDeprecated new then
      out := out.push <| ctx.finding "deprecation" d
        s!"deprecated in favor of `{new}`, which is itself deprecated"
  return out

def deprecationCheck : Check where
  name := "deprecation"
  summary := "deprecated in favor of something missing or itself deprecated"
  run := deprecation

end LeanLinter
