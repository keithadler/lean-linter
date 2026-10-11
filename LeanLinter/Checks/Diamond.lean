import LeanLinter.Basic
import LeanLinter.RunMeta
import LeanLinter.Checks.Duplicates

/-!
# `diamond`: two instances of one type that are not the same structure

`duplicate-instance` finds instances with the same type. If both give the same value, one is
redundant. If they give *different* values, instance search will pick one depending on import order
and priority, and different files will silently mean different structures by "the" structure on
that type: an instance diamond. Statements that mix the two stop being the statements anyone
thought they were.

For each group of same-typed instances, each member is compared with the first by asking Lean
whether they are definitionally equal:

* at the `instances` transparency, which is what instance search and `simp` see;
* if not, at the default transparency.

Not equal at the default transparency is a likely diamond; equal at the default but not at
`instances` is fragile, since proofs about one will not see through to the other. Instances of
`Prop`-valued classes are always equal (proof irrelevance), so only data-carrying ones can fail.
-/

open Lean Meta

namespace LeanLinter

/-- Are the instances `a` and `b`, which have the same type, definitionally equal at `mode`? -/
def instancesEqual (a b : Name) (mode : TransparencyMode) : MetaM Bool := do
  let some ca := (← getEnv).find? a | return true
  let levels := ca.levelParams.map Level.param
  forallTelescopeReducing ca.type fun xs _ => do
    withTransparency mode <| isDefEq (mkAppN (mkConst a levels) xs) (mkAppN (mkConst b levels) xs)

def diamond (ctx : Ctx) : IO (Array Finding) := do
  let isTarget (d : Decl) :=
    Meta.isInstanceCore ctx.env d.name && d.info.isDefinition && !ctx.isDeprecated d.name
      && !isPrivateName d.name
  let mut out := #[]
  for g in duplicateGroups ctx (normalizedType ·.info) isTarget (minSize := 0) do
    let first := g[0]!
    for other in g.extract 1 g.size do
      let atInstances ← tryMeta ctx.env (instancesEqual first.name other.name .instances)
      if atInstances == some true then continue
      let atDefault ← tryMeta ctx.env (instancesEqual first.name other.name .default)
      let verdict :=
        match atDefault with
        | some false => some "are not definitionally equal: a likely instance diamond"
        | some true => some "are equal only at default transparency: proofs about one will not see through to the other"
        | none => some "could not be compared in time"
      if let some v := verdict then
        out := out.push <| ctx.finding "diamond" first
          s!"`{userName first.name}` and `{userName other.name}` ({other.module}:{other.line}) have the same type but {v}"
  return out

def diamondCheck : Check where
  name := "diamond"
  summary := "two instances of one type that are not definitionally equal"
  run := diamond

end LeanLinter
