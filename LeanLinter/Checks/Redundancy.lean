import LeanLinter.Basic

/-!
# Checks for things stated, defined or kept twice

* `duplicate`: two theorems with the same statement (up to binder and universe names), each proved
  without the other. One name for a fact plus an `alias` is the usual fix.
* `duplicate-sym`: the same, where one states `a = b` (or `a ↔ b`) and the other `b = a`.
* `duplicate-instance`: two instances with the same type. Instance search tries both, and terms
  built from one do not syntactically match lemmas about the other.
* `dead-private`: a private theorem or definition that nothing refers to. Nothing outside the file
  can use it, so if the file does not, it does nothing.
-/

open Lean

namespace LeanLinter

/-- Put the two sides of a concluding `=` or `↔` in a fixed order. -/
partial def orient : Expr → Expr
  | .forallE n t b bi => .forallE n t (orient b) bi
  | e =>
    match e.getAppFn.constName?, e.getAppArgs with
    | some ``Eq, #[α, a, b] => if hash b < hash a then mkApp3 e.getAppFn α b a else e
    | some ``Iff, #[a, b] => if hash b < hash a then mkApp2 e.getAppFn b a else e
    | _, _ => e

/-- Does the proof of `d` mention any of `others`? -/
def mentionsAny (d : Decl) (others : Array Name) : Bool :=
  match d.info.value? (allowOpaque := true) with
  | some v => (usedConstants v).any (fun u => u != d.name && others.contains u)
  | none => false

/-- Number of nodes in `e`, counting up to `cap`. -/
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

def duplicateGroups (ctx : Ctx) (key : Decl → Expr) (pick : Decl → Bool) (minSize := 8) :
    Array (Array Decl) := Id.run do
  let mut groups : Std.HashMap Expr (Array Decl) := {}
  for d in ctx.decls do
    unless pick d do continue
    let k := key d
    -- `True`, `a = a` and the like say too little for two of them to be a duplicate
    if exprSize k < minSize then continue
    groups := groups.insert k ((groups.getD k #[]).push d)
  let mut out := #[]
  for (_, g) in groups.toList do
    if g.size < 2 then continue
    -- two declarations generated from one line of source are one declaration
    if (g.map fun d => (d.module, d.line)).toList.eraseDups.length < 2 then continue
    out := out.push g
  return out

private def describe (g : Array Decl) : String :=
  ", ".intercalate (g.map fun d => s!"`{userName d.name}` ({d.module}:{d.line})").toList

def duplicates (ctx : Ctx) (symmetric : Bool) : IO (Array Finding) := do
  let isThm (d : Decl) := d.info.isTheorem && !ctx.isDeprecated d.name && !Meta.isInstanceCore ctx.env d.name
  let exact := duplicateGroups ctx (fun d => normalizedType d.info) isThm
  let groups :=
    if symmetric then
      let seen : Std.HashSet Name := exact.foldl (init := {}) fun s g => g.foldl (·.insert ·.name) s
      (duplicateGroups ctx (fun d => orient (normalizedType d.info)) isThm).filter
        fun g => !g.all (seen.contains ·.name)
    else exact
  let check := if symmetric then "duplicate-sym" else "duplicate"
  let mut out := #[]
  for g in groups do
    let names := g.map (·.name)
    let independent := g.filter fun d => !mentionsAny d names
    if independent.size < 2 then continue
    out := out.push <| ctx.finding check independent[0]! s!"proved separately with the same statement: {describe independent}"
  return out

def duplicateInstances (ctx : Ctx) : IO (Array Finding) := do
  let pick (d : Decl) := Meta.isInstanceCore ctx.env d.name && !ctx.isDeprecated d.name && !isPrivateName d.name
  let mut out := #[]
  for g in duplicateGroups ctx (fun d => normalizedType d.info) pick (minSize := 0) do
    out := out.push <| ctx.finding "duplicate-instance" g[0]! s!"instances with the same type: {describe g}"
  return out

/-- Mentions something from Lean's own namespace or `IO`: meta code, used through attributes. -/
def isMetaLevel (ci : ConstantInfo) : Bool :=
  (usedConstants ci.type).any fun u => (`Lean).isPrefixOf u || (`IO).isPrefixOf u || u == `IO

def deadPrivate (ctx : Ctx) : IO (Array Finding) := do
  let candidates := ctx.decls.filter fun d =>
    isPrivateName d.name && (d.info.isTheorem || d.info.isDefinition)
      && !Meta.isInstanceCore ctx.env d.name && !isMetaLevel d.info
  let candSet : NameSet := candidates.foldl (·.insert ·.name) {}
  -- who refers to each candidate: every constant of the target modules, generated ones included
  let mut refs : Std.HashMap Name (Array Name) := {}
  let modules : Std.HashSet Name := ctx.decls.foldl (·.insert ·.module) {}
  let names := ctx.env.header.moduleNames
  for i in [0:names.size] do
    unless modules.contains names[i]! do continue
    for n in ctx.env.header.moduleData[i]!.constNames do
      let some ci := ctx.env.find? n | continue
      let mut used := usedConstants ci.type
      if let some v := ci.value? (allowOpaque := true) then used := used ++ usedConstants v
      for u in used do
        if u != n && candSet.contains u then
          refs := refs.insert u ((refs.getD u #[]).push n)
  -- a referrer that is generated from the candidate itself (its equation lemmas) is the candidate
  let owner (c r : Name) : Bool := c.isPrefixOf r
  let mut dead : NameSet := {}
  for c in candidates do
    if (refs.getD c.name #[]).all (owner c.name) then dead := dead.insert c.name
  let mut changed := true
  while changed do
    changed := false
    for c in candidates do
      if dead.contains c.name then continue
      if (refs.getD c.name #[]).all fun r => owner c.name r || dead.contains r ||
          (candidates.any fun c' => dead.contains c'.name && owner c'.name r) then
        dead := dead.insert c.name
        changed := true
  return candidates.filter (dead.contains ·.name) |>.map fun d =>
    ctx.finding "dead-private" d "private, and nothing refers to it"

end LeanLinter
