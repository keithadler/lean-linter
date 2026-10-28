import LeanLinter.Basic
import LeanLinter.Checks.Duplicates

/-!
# The same argument, made twice

* `proof-clone`: two theorems that state different things, whose compiled proofs apply the same
  lemmas, first used in the same order. The usual cause is a proof copied and edited: the same
  argument for `ℕ` and for `ℤ`, or for a statement and the same statement with one more hypothesis.
  Either the argument deserves a lemma of its own, or the two statements are one fact in two
  forms and one should be derived from the other.
* `proof-variant`: the same, where the names differ in a single word (`sum_push` and `prod_push`,
  `max_add_left` and `max_add_right`, `Array.any_eq'` and `Vector.any_eq'`). Those are almost
  always a family of lemmas written on purpose, so they are listed apart and are worth a look only
  to see whether a shared lemma would shorten the family.

How it decides. A proof is read as the list of distinct theorems it applies, in the order the term
first uses them, leaving out the plumbing every proof is full of (`Eq.symm`, `congrArg`,
`of_eq_true`, `And.intro` and so on). Two theorems are clones when those lists are equal and have
at least `minLemmas` entries. Theorems with the same statement are `duplicate`'s business and are
not reported here, nor is one whose proof mentions the other (an `alias`, a `.symm`).

Known false positives: a standard recipe that two unrelated results follow (`Nat.le_trans` through
the same four lemmas), and tactic proofs, whose terms are written by `simp` and `omega` rather than
by a person, so they say little about the argument and mostly differ from one another.
-/

open Lean

namespace LeanLinter

/-- Theorems that appear in proof terms as plumbing, not as the argument. -/
private def plumbing : List String :=
  ["Eq.symm", "Eq.trans", "Eq.mp", "Eq.mpr", "Eq.subst", "Eq.refl", "Eq.propIntro", "congrArg",
   "congrFun", "congr", "of_eq_true", "of_eq_false", "eq_self", "eq_true", "eq_false", "propext",
   "Iff.intro", "Iff.mp", "Iff.mpr", "And.intro", "And.left", "And.right", "Or.inl", "Or.inr",
   "absurd", "trivial", "rfl", "id", "ne_eq", "not_false_eq_true", "Not.elim", "False.elim",
   "HEq.refl", "cast_eq", "Classical.byContradiction", "Classical.not_not", "Nonempty.intro",
   "Exists.intro", "Subtype.property", "Decidable.byContradiction", "Decidable.decide"]

/-- The distinct theorems `e` applies, in the order its term first uses them, without plumbing. -/
def lemmaSequence (env : Environment) (e : Expr) : Array Name :=
  (usedConstants e).filter fun c =>
    match env.find? c with
    | some (.thmInfo _) => !isGeneratedName c && !plumbing.contains (toString c)
    | _ => false

/-- How many distinct lemmas a proof applies before its argument says enough to compare. -/
def minLemmas : Nat := 5

private def describeGroup (g : Array Decl) : String :=
  ", ".intercalate (g.map fun d => s!"`{userName d.name}` ({d.module}:{d.line})").toList

/-- The words of a declaration's name: its components, each split at `_`. -/
private def nameWords (n : Name) : Array String :=
  (toString (userName n)).splitOn "." |>.foldl (fun acc c => acc ++ c.splitOn "_") [] |>.filter (· ≠ "") |>.toArray

/-- Do all the names have the same number of words, and differ in at most one position? -/
def isVariantFamily (names : Array Name) : Bool :=
  let ws := names.map nameWords
  match ws[0]? with
  | none => false
  | some w0 =>
    ws.all (·.size == w0.size) &&
      (List.range w0.size).countP (fun i => ws.any fun w => w[i]! != w0[i]!) ≤ 1

/-- The groups of theorems with different statements that apply the same lemmas in the same order,
split into those whose names differ in one word (`variants`) and the rest. -/
def proofCloneGroups (ctx : Ctx) (variants : Bool) : Array (Nat × Array Decl) := Id.run do
  let mut groups : Std.HashMap (Array Name) (Array Decl) := {}
  for d in ctx.decls do
    unless d.info.isThm && !ctx.isDeprecated d.name && !Meta.isInstanceCore ctx.env d.name do
      continue
    let some v := d.info.value? (allowOpaque := true) | continue
    let key := lemmaSequence ctx.env v
    if key.size < minLemmas then continue
    groups := groups.insert key ((groups.getD key #[]).push d)
  let mut out := #[]
  for (key, g) in groups.toList do
    let sources := (g.map fun d => (d.module, d.line)).toList.eraseDups
    let statements := (g.map (normalizedType ·.info)).toList.eraseDups
    if g.size < 2 || sources.length < 2 || statements.length < 2 then continue
    let independent := g.filter (!mentionsAny · (g.map (·.name)))
    if independent.size < 2 then continue
    if isVariantFamily (independent.map (·.name)) != variants then continue
    let ordered := independent.qsort fun a b =>
      a.module.toString < b.module.toString || (a.module == b.module && a.line < b.line)
    out := out.push (key.size, ordered)
  return out

def proofClones (variants : Bool) (ctx : Ctx) : IO (Array Finding) := do
  let check := if variants then "proof-variant" else "proof-clone"
  let what := if variants then "a family of variants" else "the same argument under different names"
  let out := (proofCloneGroups ctx variants).map fun (n, g) =>
    ctx.finding check g[0]!
      s!"different statements, but the proofs apply the same {n} lemmas in the same order ({what}): {describeGroup g}"
  return out.qsort fun a b =>
    a.module.toString < b.module.toString || (a.module == b.module && a.line < b.line)

def proofCloneCheck : Check where
  name := "proof-clone"
  summary := "two theorems with different statements and different names whose proofs apply the same lemmas in the same order"
  run := proofClones false

def proofVariantCheck : Check where
  name := "proof-variant"
  summary := "the same, where the names differ in one word: a family of lemmas written on purpose"
  run := proofClones true

end LeanLinter
