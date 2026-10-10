import LeanLinter.Basic

/-!
# `dead-private`: private declarations nothing uses

Nothing outside a file can use its private declarations, so a private theorem or definition that
nothing in the library refers to does nothing. Such declarations are usually helpers left behind
when the proof that needed them changed.

## How it decides

Every constant of the target modules is scanned, generated ones included, for the private
candidates its type and value mention. A candidate is dead when everything that mentions it is
either generated from it (its own equation lemmas, say) or dead itself, so chains of helpers that
only feed each other are reported together.

Instances, and declarations whose type mentions `Lean` or `IO` (tactics, elaborators and other
code run through attributes), are not candidates: what uses them never names them in a term.

## False positives

Lemmas registered with an attribute and used only by a tactic that looks them up by name (an
`aesop` rule set, a `simproc`) are used without being mentioned, and are reported.
-/

open Lean

namespace LeanLinter

/-- Is this declaration used by code rather than by terms (tactics, elaborators, `IO`)? -/
def isMetaLevel (ci : ConstantInfo) : Bool :=
  (usedConstants ci.type).any fun c => (`Lean).isPrefixOf c || c == `IO || (`IO).isPrefixOf c

/-- The candidate that `n` was generated from, if any: `n` itself or its nearest prefix in
`candidates` (the owner of `foo.eq_1` is `foo`). -/
partial def owner? (candidates : NameSet) (n : Name) : Option Name :=
  if n.isAnonymous then none
  else if candidates.contains n then some n
  else owner? candidates n.getPrefix

def deadPrivate (ctx : Ctx) : IO (Array Finding) := do
  let candidates := ctx.decls.filter fun d =>
    isPrivateName d.name && (d.info.isTheorem || d.info.isDefinition)
      && !Meta.isInstanceCore ctx.env d.name && !isMetaLevel d.info
  let candidateSet : NameSet := candidates.foldl (·.insert ·.name) {}
  -- For each candidate, the owners of the constants that mention it (a constant that is not
  -- generated from a candidate is its own owner).
  let mut users : Std.HashMap Name (Array Name) := {}
  let targetModules : Std.HashSet Name := ctx.decls.foldl (·.insert ·.module) {}
  for mod in ctx.env.header.moduleNames, data in ctx.env.header.moduleData do
    unless targetModules.contains mod do continue
    for n in data.constNames do
      let some ci := ctx.env.find? n | continue
      let mentioned := usedConstants ci.type ++ ((ci.value? (allowOpaque := true)).map usedConstants).getD #[]
      let user := (owner? candidateSet n).getD n
      for c in mentioned do
        if c != user && candidateSet.contains c then
          users := users.insert c ((users.getD c #[]).push user)
  -- A candidate is dead once every user is dead; start from those with no users at all.
  let mut dead : NameSet := {}
  let mut changed := true
  while changed do
    changed := false
    for d in candidates do
      if !dead.contains d.name && (users.getD d.name #[]).all dead.contains then
        dead := dead.insert d.name
        changed := true
  return candidates.filter (dead.contains ·.name) |>.map fun d =>
    ctx.finding "dead-private" d "private, and nothing refers to it"

def deadPrivateCheck : Check where
  name := "dead-private"
  summary := "a private theorem or definition that nothing refers to"
  run := deadPrivate

end LeanLinter
