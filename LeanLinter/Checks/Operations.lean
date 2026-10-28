import LeanLinter.Basic

/-!
# `op-mismatch`: the name says one operation, the statement uses another

A lemma named `foo_mul_bar` should multiply something. When its statement contains no
multiplication at all, but does contain, say, an addition, the name was probably copied from a
neighboring lemma and not updated, or the statement was changed and the name was not. In Mathlib,
`Multiset.add_sub_cancel` and `Multiset.sub_add_cancel` were once on a list of names that
disagree with their statements.

## How it decides

Each *operation word* (`add`, `mul`, `sub`, `div`, `sum`, `prod`, `mod`) has the constants that
implement it (`HAdd.hAdd`, `Finset.sum`, ...). Report a theorem when its name contains an operation
word, its statement mentions none of that word's constants, and it does mention the constants of
a word it is easily confused with (`add` and `sub`, `sum` and `prod`, ...) that the name lacks.
Operations that routinely stand in for each other (`mul` and `smul`, `inv` and `div`) are not paired.

## False positives

Operations hidden inside a definition do not show up in the statement: `Commute a b` is a
multiplication, but the statement `Commute a b ↔ ...` contains no `hMul`. Such a lemma is reported
only when it also uses some *other* operation, which keeps these rare.
-/

open Lean

namespace LeanLinter

/-- An operation word of a lemma name, with the last components of the constants that implement
it (first letter lowered, as `lowFirst` gives them). -/
def opWords : List (String × List String) :=
  [("add", ["add", "hAdd"]), ("mul", ["mul", "hMul"]), ("sub", ["sub", "hSub"]),
   ("div", ["div", "hDiv"]), ("sum", ["sum", "tsum", "finsum"]),
   ("prod", ["prod", "tprod", "finprod"]), ("mod", ["mod", "hMod"])]

/-- Pairs of operations that are easily swapped by mistake, as opposed to ones that routinely
stand in for each other (`mul` and `smul`, `inv` and `div`, `right_inv`). -/
def confusable : List (String × String) :=
  [("add", "sub"), ("add", "mul"), ("mul", "div"), ("sum", "prod"), ("div", "mod")]

def isConfusable (a b : String) : Bool :=
  confusable.any fun (x, y) => (x == a && y == b) || (x == b && y == a)

/-- Pairs of words that `to_additive` swaps in names. -/
def additiveSwaps : List (String × String) :=
  [("Add", "Mul"), ("add", "mul"), ("Sub", "Div"), ("sub", "div"), ("sum", "prod"), ("Sum", "Prod"),
   ("nsmul", "pow"), ("zsmul", "zpow"), ("vadd", "smul"), ("zero", "one"), ("Zero", "One"),
   ("neg", "inv"), ("Neg", "Inv")]

/-- Does the declaration have a multiplicative twin? Then it was produced by `to_additive`, and the
constants inside it keep their original names, which makes the operation words in its name
unreliable. `AddSubgroup.center_sum` has the twin `Subgroup.center_prod`. -/
def hasTwin (env : Environment) (n : Name) : Bool :=
  let s := toString (userName n)
  let swapped := additiveSwaps.foldl (fun s (a, b) => s.replace a b) s
  -- `AddSubgroup` ↔ `Subgroup`, `AddAction` ↔ `MulAction`
  let candidates := [swapped, swapped.replace "Mul" "", swapped.replace "AddMul" "Mul",
    s.replace "Add" "", s.replace "Add" "Mul"]
  candidates.any fun c => c != s && env.contains c.toName

def opMismatch (ctx : Ctx) : IO (Array Finding) := do
  let mut out := #[]
  for d in ctx.decls do
    unless d.info.isThm && !ctx.isDeprecated d.name do continue
    -- words after `of` describe hypotheses, and `neg` in `ediv_neg_of_neg` means "negative"
    let all := nameTokens d.name |>.map fun w => String.ofList (w.toList.filter (· != '\''))
    let words := all.toList.takeWhile (· != "of") |>.toArray
    if hasTwin ctx.env d.name then continue
    -- the exact last component: `Finset.prod` is the operation, `Prod` is a type
    let usedLast : Array String := (usedConstants d.info.type).map lastString
    -- `divByMonic` and `addCommutator` count as division and addition
    let uses (aliases : List String) :=
      usedLast.any fun u => aliases.any fun a =>
        u == a || (u.startsWith a && (u.drop a.length).front?.any fun c => c.isUpper || c == '\'')
          -- the types `Prod` and `Sum`: "tsum_prod" is a sum over a product type
          || (a == "prod" && u == "Prod") || (a == "sum" && u == "Sum")
    for (word, aliases) in opWords do
      if !words.contains word || uses aliases then continue
      let others := opWords.filter fun (w, a) => !words.contains w && isConfusable word w && uses a
      if let some (other, _) := others.head? then
        out := out.push <| ctx.finding "op-mismatch" d
          s!"the name says `{word}`, but the statement has no `{word}` and does use `{other}`"
  return out

def opMismatchCheck : Check where
  name := "op-mismatch"
  summary := "the name says `mul`, `add`, `sum`..., but the statement uses a different operation"
  run := opMismatch

end LeanLinter
