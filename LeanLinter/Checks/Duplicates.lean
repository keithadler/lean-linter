import LeanLinter.Basic

/-!
# Things stated twice

* `duplicate`: two theorems with the same statement, up to the names of bound variables and
  universes, each proved without the other. In Mathlib, Dedekind's lemma (algebra homomorphisms are
  linearly independent) is proved twice, in two files under two names.
* `duplicate-sym`: the same, where one states `a = b` (or `a ↔ b`) and the other `b = a`.
* `duplicate-instance`: two instances of the same type. Instance search tries both, and a term
  built from one does not match lemmas stated about the other.

A theorem whose proof mentions the other (an `alias`, a `.symm`) is a deliberate second name, not a
duplicate, and is not reported. Neither are statements too small to mean much (`True`, `a = a`),
nor several declarations generated from one line of source.
-/

open Lean

namespace LeanLinter

/-- Put the two sides of a concluding `=` or `↔` in a fixed order, so that a statement and its
symmetric version compare equal. -/
partial def orient : Expr → Expr
  | .forallE n t b bi => .forallE n t (orient b) bi
  | e =>
    match e.getAppFn.constName?, e.getAppArgs with
    | some ``Eq, #[α, a, b] => if hash b < hash a then mkApp3 e.getAppFn α b a else e
    | some ``Iff, #[a, b] => if hash b < hash a then mkApp2 e.getAppFn b a else e
    | _, _ => e

/-- The number of nodes of `e`, counted up to `cap`. -/
partial def exprSize (e : Expr) (cap : Nat := 12) : Nat :=
  go e 0
where
  go (e : Expr) (n : Nat) : Nat :=
    if n ≥ cap then n else
    match e with
    | .app f a => go a (go f (n + 1))
    | .lam _ t b _ | .forallE _ t b _ => go b (go t (n + 1))
    | .letE _ t v b _ => go b (go v (go t (n + 1)))
    | .mdata _ b | .proj _ _ b => go b (n + 1)
    | _ => n + 1

/-- Does the proof or value of `d` mention one of `others`? -/
def mentionsAny (d : Decl) (others : Array Name) : Bool :=
  match d.info.value? (allowOpaque := true) with
  | some v => (usedConstants v).any fun c => c != d.name && others.contains c
  | none => false

/-- The declarations satisfying `pick`, grouped by `key`, keeping groups of two or more that come
from at least two lines of source and whose key has at least `minSize` nodes. -/
def duplicateGroups (ctx : Ctx) (key : Decl → Expr) (pick : Decl → Bool) (minSize := 8) :
    Array (Array Decl) := Id.run do
  let mut groups : Std.HashMap Expr (Array Decl) := {}
  for d in ctx.decls do
    unless pick d do continue
    let k := key d
    if exprSize k < minSize then continue
    groups := groups.insert k ((groups.getD k #[]).push d)
  return groups.fold (init := #[]) fun out _ g =>
    let sources := (g.map fun d => (d.module, d.line)).toList.eraseDups
    if g.size ≥ 2 && sources.length ≥ 2 then out.push g else out

/-- `` `a` (Module:12), `b` (Other:34) `` -/
private def describe (g : Array Decl) : String :=
  ", ".intercalate (g.map fun d => s!"`{userName d.name}` ({d.module}:{d.line})").toList

/-- Theorems proved separately with the same statement; with `symmetric`, only the groups that
appear once the two sides of `=` and `↔` are put in order. -/
def duplicates (symmetric : Bool) (ctx : Ctx) : IO (Array Finding) := do
  let isTarget (d : Decl) :=
    d.info.isThm && !ctx.isDeprecated d.name && !Meta.isInstanceCore ctx.env d.name
  let exact := duplicateGroups ctx (normalizedType ·.info) isTarget
  let groups :=
    if symmetric then
      let alreadyExact : NameSet := exact.foldl (fun s g => g.foldl (·.insert ·.name) s) {}
      (duplicateGroups ctx (orient <| normalizedType ·.info) isTarget).filter
        (!·.all (alreadyExact.contains ·.name))
    else exact
  let check := if symmetric then "duplicate-sym" else "duplicate"
  return groups.filterMap fun g =>
    let independent := g.filter (!mentionsAny · (g.map (·.name)))
    if independent.size < 2 then none
    else some <| ctx.finding check independent[0]!
      s!"proved separately with the same statement: {describe independent}"

def duplicateInstances (ctx : Ctx) : IO (Array Finding) := do
  let isTarget (d : Decl) :=
    Meta.isInstanceCore ctx.env d.name && !ctx.isDeprecated d.name && !isPrivateName d.name
  return (duplicateGroups ctx (normalizedType ·.info) isTarget (minSize := 0)).map fun g =>
    ctx.finding "duplicate-instance" g[0]! s!"instances with the same type: {describe g}"

def duplicateCheck : Check where
  name := "duplicate"
  summary := "two theorems with the same statement, each proved without the other"
  run := duplicates false

def duplicateSymCheck : Check where
  name := "duplicate-sym"
  summary := "two theorems with the same statement, one of them stated backwards"
  run := duplicates true

def duplicateInstanceCheck : Check where
  name := "duplicate-instance"
  summary := "two instances of the same type"
  run := duplicateInstances

end LeanLinter
