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

Words after `_of_` name hypotheses (`surjective_of_injective`), so only the words before the
first `of` are read. A lemma whose conclusion is its own namespace (`Antitone.comp_monotone`
concluding `Antitone`) uses the namespace for dot notation and is skipped.
-/

open Lean

namespace LeanLinter

/-- Properties that come in families: a lemma named for one should not conclude another. -/
def propertyFamilies : List (List String) :=
  [["injective", "surjective", "bijective"], ["monotone", "antitone", "strictMono", "strictAnti"]]

/-- What is wrong, if anything, with a lemma whose name ends in `word` and whose conclusion `c` has
head constant `head`. -/
def shapeProblem? (word : String) (c : Expr) (head : Name) : Option String :=
  let h := lowFirst (lastString head)
  if (word == "lt" || word == "pos") && head == ``LE.le && !mentionsLast c "lt" then
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
    unless d.info.isTheorem && !ctx.isDeprecated d.name do continue
    let some word := ((nameTokens d.name).toList.takeWhile (· != "of")).getLast? | continue
    let c := conclusion d.info.type
    let some head := c.getAppFn.constName? | continue
    if head == (userName d.name).getPrefix then continue
    if let some message := shapeProblem? word c head then
      out := out.push <| ctx.finding "name-shape" d message
  return out

def nameShapeCheck : Check where
  name := "name-shape"
  summary := "`_iff`, `_lt`, `_le`, `_injective`, `_monotone`... but the conclusion is something else"
  run := nameShape

end LeanLinter
