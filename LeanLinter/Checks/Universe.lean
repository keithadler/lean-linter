import LeanLinter.Basic

/-!
# `universe`: a lemma needlessly restricted to `Type`

A lemma with a binder `{α : Type}` cannot be used for a type in any higher universe: `Type 1`
and above are out of reach, although nothing in the statement needs `α` to be small. Mathlib
writes `Type*` for this reason. A restricted lemma still compiles and still passes every test that
happens to use small types, so it is only found when somebody needs the general case and cannot
have it.

## How it decides

Report a theorem or definition whose type has a binder `α : Type` (exactly `Type 0`) *and* no
universe parameters at all: nothing in it is universe polymorphic, which is what a forgotten
`Type*` looks like. Declarations about concrete objects (`ℕ`, `ℝ`) have no such binder and are not
reported. Private declarations, and modules about tactics and meta-programming (where `Type` is the
right universe), are skipped. A file with eight or more such declarations is reported once, since
the fix is one edit. Small-category statements that need `Type` on purpose still show up and need a
look.
-/

open Lean

namespace LeanLinter

/-- Is `e` exactly `Type` (`Sort 1`)? -/
def isTypeZero (e : Expr) : Bool :=
  match e with
  | .sort (.succ .zero) => true
  | _ => false

/-- Modules about tactics, meta-programming and the like, where `Type` is the right universe. -/
def isMetaModule (m : Name) : Bool :=
  m.components.any fun c => ["Tactic", "Meta", "Lean", "Util", "Command", "Elab", "Widget", "Mathport",
    "Testing", "Computability", "Control", "Init"].contains (toString c)

def universeRestricted (ctx : Ctx) : IO (Array Finding) := do
  let mut byModule : Std.HashMap Name (Array Decl) := {}
  for d in ctx.decls do
    unless (d.info.isThm || d.info.isDefinition) && !ctx.isDeprecated d.name do continue
    if isPrivateName d.name || isMetaModule d.module || !d.info.levelParams.isEmpty then continue
    if (binderDomains' d.info.type).any isTypeZero then
      byModule := byModule.insert d.module ((byModule.getD d.module #[]).push d)
  let mut out := #[]
  for (_, ds) in byModule.toList do
    let ds := ds.qsort (·.line < ·.line)
    if ds.size ≥ 8 then
      -- the whole file fixes `α : Type`: one finding, since it is one edit
      out := out.push <| ctx.finding "universe" ds[0]!
        s!"{ds.size} declarations in this file are restricted to `Type`, with no universe parameters"
    else
      for d in ds do
        out := out.push <| ctx.finding "universe" d "a binder of type `Type` and no universe parameters: it cannot be used at a higher universe"
  return out
where
  binderDomains' : Expr → Array Expr
    | .forallE _ d b _ => #[d] ++ binderDomains' b
    | .mdata _ b => binderDomains' b
    | _ => #[]

def universeCheck : Check where
  name := "universe"
  summary := "a binder `α : Type` and no universe parameters: restricted to the smallest universe"
  run := universeRestricted

end LeanLinter
