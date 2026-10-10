import LeanLinter.Basic

/-!
# `mislabel`: the name says one thing, the statement says its opposite

A lemma copied from its neighbor sometimes keeps the neighbor's name: `homEquivLeft_symm_apply`
stating a fact about `homEquivRight`, `AntitoneOn.monotone` concluding `Antitone`. This check
looks at each constant the statement mentions; when the lemma's name mentions that constant's
opposite (`Left`/`Right`, `fst`/`snd`, `inl`/`inr`, `Monotone`/`Antitone`, ...), the statement
never mentions the opposite, and the opposite is a real constant, the name and the statement
disagree.
-/

open Lean

namespace LeanLinter

/-- Words whose swap turns a constant into its mirror image. -/
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

/-- `s` with one occurrence of `a` replaced by `b`, for each occurrence. -/
def replaceEach (s a b : String) : List String :=
  let parts := s.splitOn a
  (List.range (parts.length - 1)).map fun i =>
    let (pre, post) := parts.splitAt (i + 1)
    a.intercalate pre ++ b ++ a.intercalate post

/-- Every name obtained from `s` by swapping one word for its opposite. -/
def mirrors (s : String) : List String :=
  opposites.foldl (init := []) fun acc (a, b) =>
    acc ++ replaceEach s a b ++ replaceEach s b a

def mislabel (ctx : Ctx) : IO (Array Finding) := do
  let mut out := #[]
  for d in ctx.decls do
    let .thmInfo _ := d.info | continue
    if ctx.isDeprecated d.name then continue
    let tokens := nameTokens d.name
    let used := usedConstants d.info.type
    let usedLast : Std.HashSet String := used.foldl (init := {}) fun s u => s.insert (lowFirst (lastString u))
    for u in used do
      -- an instance in a statement is an implicit argument, not something a name refers to
      if Meta.isInstanceCore ctx.env u || (lastString u).startsWith "inst" then continue
      if (ctx.env.find? u).any (·.isTheorem) then continue
      let ul := lastString u
      if ul.length < 3 || tokens.contains (lowFirst ul) then continue
      for m in mirrors ul do
        if tokens.contains (lowFirst m) && !usedLast.contains (lowFirst m)
            && ctx.env.contains (u.getPrefix.str m) then
          out := out.push <| ctx.finding "mislabel" d
            s!"the name says `{u.getPrefix.str m}` but the statement uses `{u}` and never `{m}`"
  return out

end LeanLinter
