import LeanLinter.Basic
import LeanLinter.Checks.Duplicates

/-!
# The same argument, made twice

* `proof-clone`: two theorems that state different things, whose compiled proofs apply the same
  lemmas, first used in the same order. The usual cause is a proof copied and edited: the same
  argument for `ℕ` and for `ℤ`, or for a statement and the same statement with one more hypothesis.
  Either the argument deserves a lemma of its own, or the two statements are one fact in two
  forms and one should be derived from the other.

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

/-- Theorems with different statements that apply the same lemmas in the same order. -/
def proofClones (ctx : Ctx) : IO (Array Finding) := do
  let mut groups : Std.HashMap (Array Name) (Array Decl) := {}
  for d in ctx.decls do
    unless d.info.isTheorem && !ctx.isDeprecated d.name && !Meta.isInstanceCore ctx.env d.name do
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
    out := out.push <| ctx.finding "proof-clone" independent[0]!
      s!"different statements, but the proofs apply the same {key.size} lemmas in the same order: {describeGroup independent}"
  return out.qsort fun a b =>
    a.module.toString < b.module.toString || (a.module == b.module && a.line < b.line)

def proofCloneCheck : Check where
  name := "proof-clone"
  summary := "two theorems with different statements whose proofs apply the same lemmas in the same order"
  run := proofClones

end LeanLinter
