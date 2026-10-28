import LeanLinter.Basic

/-!
# `name-shape`: the name promises a conclusion the statement does not have

Mathlib's naming convention makes a lemma's last word describe its conclusion: `foo_iff` is an
`↔`, `foo_lt` concludes a `<`, `foo_injective` concludes `Function.Injective`. When the conclusion
is something else, either the name is wrong or the lemma is not the one its name promises: in
Mathlib, `DFinsupp.coe_strictMono` is a copy of `coe_mono` and concludes plain `Monotone`, so
the strict version its name promises does not exist.

## What is reported

* a name ending in `_iff` whose conclusion is neither `↔` nor `=` and contains no `↔`;
* a name ending in `_lt` or `_pos` (strict) whose conclusion is a `≤` with no `<`;
* a name ending in `_le` or `_nonneg` whose conclusion is a strict `<`;
* a name ending in one property of a family (`injective`, `surjective`, `bijective`;
  `monotone`, `antitone`, `strictMono`, `strictAnti`) whose conclusion is another member.

## What is not

`n + 1 ≤ m` is how `n < m` is written on `Nat`, so a `_lt` lemma concluding it is correct. In
`foo_mono_pos` the word `pos` says where the lemma holds ("on the positives"), not that it
concludes something strict, so `_pos` after `mono`, `monotone`, `anti`, `antitone`, `strictMono`
or `strictAnti` is not read as strict.

Words after `_of_` name hypotheses (`surjective_of_injective`), so only the words before the
first `of` are read. A lemma whose conclusion is its own namespace (`Antitone.comp_monotone`
concluding `Antitone`) uses the namespace for dot notation and is skipped.
-/

open Lean

namespace LeanLinter

/-- Properties that come in families: a lemma named for one should not conclude another. -/
def propertyFamilies : List (List String) :=
  [["injective", "surjective", "bijective"], ["monotone", "antitone", "strictMono", "strictAnti"]]

/-- Words after which `pos` means "on the positives" and says nothing about strictness. -/
def monoWords : List String :=
  ["mono", "monotone", "anti", "antitone", "strictMono", "strictAnti", "monotoneOn", "antitoneOn"]

/-- Is `c` of the form `x + 1 ≤ y` or `Nat.succ x ≤ y`, which is `x < y` written out? -/
def isSuccLe (c : Expr) : Bool :=
  match c.getAppFn, c.getAppArgs with
  | .const ``LE.le _, #[_, _, lhs, _] =>
    lhs.isAppOf ``Nat.succ ||
      (lhs.isAppOf ``HAdd.hAdd && match lhs.getAppArgs.back? with
        | some r => r.isAppOf ``OfNat.ofNat && r.getAppNumArgs ≥ 2 && (r.getArg! 1).rawNatLit? == some 1
        | none => false)
  | _, _ => false

/-- What is wrong, if anything, with a lemma whose name ends in `word` and whose conclusion `c` has
head constant `head`. -/
def shapeProblem? (word : String) (c : Expr) (head : Name) (prev : Option String := none) : Option String :=
  let h := lowFirst (lastString head)
  if (word == "lt" || word == "pos") && head == ``LE.le && !mentionsLast c "lt" && !isSuccLe c
      && !(word == "pos" && prev.any (monoWords.contains ·)) then
    some s!"the name ends in `_{word}` (strict), but the conclusion is a `≤`"
  else if (word == "le" || word == "nonneg") && head == ``LT.lt then
    some s!"the name ends in `_{word}`, but the conclusion is a strict `<`"
  else if word == "iff" then
    if head == ``Iff || head == ``Eq || mentionsLast c "Iff" then none
    else some s!"the name ends in `_iff`, but the conclusion is a `{head}` and contains no `↔`"
  else
    propertyFamilies.findSome? fun family =>
      if family.contains word && family.any (fun p => p != word && (h == p || h == p ++ "On")) then
        some s!"the name says `{word}`, but the conclusion is `{head}`"
      else none

def nameShape (ctx : Ctx) : IO (Array Finding) := do
  let mut out := #[]
  for d in ctx.decls do
    unless d.info.isThm && !ctx.isDeprecated d.name do continue
    let toks := (nameTokens d.name).toList.takeWhile (· != "of")
    let some word := toks.getLast? | continue
    let prev := if toks.length ≥ 2 then toks[toks.length - 2]? else none
    let c := conclusion d.info.type
    let some head := c.getAppFn.constName? | continue
    if head == (userName d.name).getPrefix then continue
    if let some message := shapeProblem? word c head prev then
      out := out.push <| ctx.finding "name-shape" d message
  return out

def nameShapeCheck : Check where
  name := "name-shape"
  summary := "`_iff`, `_lt`, `_le`, `_injective`, `_monotone`... but the conclusion is something else"
  run := nameShape

end LeanLinter
