import LeanLinter.Basic

/-!
# `vacuous`: a statement that says nothing

A theorem can compile, and be fully proved, and still assert nothing:

* its conclusion is `True`, or says that something equals itself (`x = x`, `p ↔ p`);
* it has a hypothesis `False`, so it holds of anything;
* two of its hypotheses contradict each other (`h : p` and `h' : ¬p`), so nothing can satisfy them.

The last two make the statement vacuously true: the proof is real, but it proves nothing about the
objects it is named after. This is a classic mistake in hand-written formalizations of hard theorems,
and the reason for checking a formal statement by reading it and not only by checking its proof.

Names containing `refl`, `rfl`, `self`, `id`, `false`, `absurd`, `elim`, `contra`, `not` or `ne`
are left alone, since stating `a = a` or `p → ¬p → q` is the point of those lemmas.
-/

open Lean

namespace LeanLinter

/-- Words in a lemma name that mean it is *meant* to state something trivial or contradictory. -/
def intendedTrivial : List String :=
  ["refl", "rfl", "self", "id", "false", "absurd", "elim", "contra", "not", "ne", "irrefl", "empty",
   "of", "imp", "mt", "contrapose", "trivial", "true"]

/-- The binder domains of `e`, each with the number of binders in front of it. -/
partial def binderDomains (e : Expr) (depth : Nat := 0) : Array (Nat × Expr) :=
  match e with
  | .forallE _ d b _ => #[(depth, d)] ++ binderDomains b (depth + 1)
  | .mdata _ b => binderDomains b depth
  | _ => #[]

/-- Is `b` the negation of `a`, where `b` sits `gap` binders after `a`? -/
def negates (a b : Expr) (gap : Nat) : Bool :=
  let a := a.liftLooseBVars 0 gap
  match b with
  | .app (.const ``Not _) x => x == a
  | .forallE _ x (.const ``False _) _ => x == a
  | _ => false

def vacuous (ctx : Ctx) : IO (Array Finding) := do
  let mut out := #[]
  for d in ctx.decls do
    unless d.info.isTheorem && !ctx.isDeprecated d.name do continue
    let words := nameTokens d.name
    if words.any intendedTrivial.contains || ctx.env.isProjectionFn d.name then continue
    let c := conclusion d.info.type
    let args := c.getAppArgs
    if c.isConstOf ``True then
      out := out.push <| ctx.finding "vacuous" d "the conclusion is `True`"
    else if c.getAppFn.constName? == some ``Eq && args.size == 3 && args[1]! == args[2]! then
      out := out.push <| ctx.finding "vacuous" d "both sides of the conclusion are the same term (is it only unfolding an abbreviation?)"
    else if c.getAppFn.constName? == some ``Iff && args.size == 2 && args[0]! == args[1]! then
      out := out.push <| ctx.finding "vacuous" d "the conclusion is `p ↔ p`"
    let doms := binderDomains d.info.type
    if doms.any (·.2.isConstOf ``False) then
      out := out.push <| ctx.finding "vacuous" d "a hypothesis is `False`"
    else
      for (i, a) in doms do
        if let some (_, _) := doms.find? fun (j, b) => j > i && negates a b (j - i) then
          out := out.push <| ctx.finding "vacuous" d "two hypotheses contradict each other (`p` and `¬p`)"
          break
  return out

def vacuousCheck : Check where
  name := "vacuous"
  summary := "the conclusion is trivial, or the hypotheses are contradictory"
  run := vacuous

end LeanLinter
