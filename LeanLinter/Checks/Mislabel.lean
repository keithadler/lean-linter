import LeanLinter.Basic

/-!
# `mislabel`: the name says one thing, the statement says its opposite

A lemma copied from its neighbor sometimes keeps the neighbor's name. In Mathlib,
`HoCat.homEquivLeft_symm_apply` stated a fact about `homEquivRight`, and `AntitoneOn.monotone`
concludes `Antitone`. The type checker cannot notice, because the statement is true; only the
name is wrong, so whoever looks for the lemma by name finds the wrong fact or none.

## How it decides

For each theorem, take each constant `c` its statement mentions, and each *mirror* of `c`: the
name obtained by swapping one word of `c`'s last component for its opposite (`Left`/`Right`,
`fst`/`snd`, `Monotone`/`Antitone`, see `opposites`). Report when

* the theorem's name contains the mirror as one of its `_`-separated words,
* the name does not contain `c` itself,
* the statement never mentions anything whose last component is the mirror, and
* the mirror is a real constant next to `c` (same namespace).

Instances and theorems in the statement are skipped: they are implicit arguments and proofs, not
what a name refers to.

## False positives

The opposite words also have unrelated meanings. `_odd` can name the parity of an index whose
statement uses `Even`; "limit" can mean a limit ordinal in a lemma about `colimit`; `pred` can
name `n - 1` in a lemma using `succ`. Each finding needs a look.
-/

open Lean

namespace LeanLinter

/-- Pairs of words whose swap turns a constant's name into its mirror image. -/
def opposites : List (String × String) :=
  [("Left", "Right"), ("left", "right"), ("Fst", "Snd"), ("fst", "snd"), ("inl", "inr"),
   ("Inl", "Inr"), ("top", "bot"), ("Top", "Bot"), ("sup", "inf"), ("Sup", "Inf"),
   ("iSup", "iInf"), ("sSup", "sInf"), ("max", "min"), ("Max", "Min"), ("Ioi", "Iio"),
   ("Ici", "Iic"), ("Ioc", "Ico"), ("succ", "pred"), ("Succ", "Pred"), ("mono", "epi"),
   ("Mono", "Epi"), ("initial", "terminal"), ("Initial", "Terminal"), ("limit", "colimit"),
   ("Limit", "Colimit"), ("kernel", "cokernel"), ("Kernel", "Cokernel"),
   ("injective", "surjective"), ("Injective", "Surjective"), ("atTop", "atBot"),
   ("monotone", "antitone"), ("Monotone", "Antitone"), ("StrictMono", "StrictAnti"),
   ("upper", "lower"), ("Upper", "Lower"), ("even", "odd"), ("Even", "Odd"),
   ("toDual", "ofDual"), ("hom", "inv"), ("map", "comap"), ("image", "preimage"),
   ("Pi", "Sigma"), ("nhdsLT", "nhdsGT"), ("nhdsLE", "nhdsGE"), ("unit", "counit"),
   ("Unit", "Counit"), ("lift", "desc"), ("ι", "π"), ("head", "last"), ("Closed", "Open"),
   ("closed", "open"), ("Bdd", "Unbdd"), ("Above", "Below"), ("upperBounds", "lowerBounds"),
   ("Lt", "Gt"), ("Le", "Ge")]

/-- `s` with one occurrence of `a` replaced by `b`, once for each occurrence:
`replaceEach "LeftLeft" "Left" "Right" = ["RightLeft", "LeftRight"]`. -/
def replaceEach (s a b : String) : List String :=
  let parts := s.splitOn a
  (List.range (parts.length - 1)).map fun i =>
    let (pre, post) := parts.splitAt (i + 1)
    a.intercalate pre ++ b ++ a.intercalate post

/-- Every string obtained from `s` by swapping one word for its opposite, in either direction. -/
def mirrors (s : String) : List String :=
  opposites.foldl (init := []) fun acc (a, b) => acc ++ replaceEach s a b ++ replaceEach s b a

/-- Is `c` something a lemma's name could refer to? Instances are implicit arguments and theorems
are proofs, so neither is. -/
private def nameable (env : Environment) (c : Name) : Bool :=
  !(Meta.isInstanceCore env c || (lastString c).startsWith "inst" || (env.find? c).any (·.isTheorem))

def mislabel (ctx : Ctx) : IO (Array Finding) := do
  let mut out := #[]
  for d in ctx.decls do
    unless d.info.isTheorem && !ctx.isDeprecated d.name do continue
    let words := nameTokens d.name
    let used := usedConstants d.info.type
    let usedLast : Std.HashSet String := used.foldl (·.insert <| lowFirst <| lastString ·) {}
    for c in used do
      let last := lastString c
      if last.length < 3 || words.contains (lowFirst last) || !nameable ctx.env c then continue
      for m in mirrors last do
        let mirror := c.getPrefix.str m
        if words.contains (lowFirst m) && !usedLast.contains (lowFirst m) && ctx.env.contains mirror then
          out := out.push <| ctx.finding "mislabel" d
            s!"the name says `{mirror}` but the statement uses `{c}` and never `{m}`"
  return out

def mislabelCheck : Check where
  name := "mislabel"
  summary := "the name names a constant, but the statement uses only its opposite"
  run := mislabel

end LeanLinter
