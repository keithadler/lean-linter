import LeanLinter.Basic

/-!
# Docstrings that disagree with the code

* `doc-mislabel`: the docstring names one property of a family ("injective", "monotone", "open")
  when the statement concludes another. In Mathlib, the docstring of
  `antitone_of_odd_of_monotoneOn_nonneg` says "monotone on `Set.Ici 0`" about a hypothesis that is
  `AntitoneOn`.
* `doc-refs`: the docstring names, in backticks, a declaration that does not exist, usually one
  renamed or deleted since. In Mathlib, a docstring still pointed at `Submodule.basisOfPidOfLe`,
  which had been renamed to `basisOfPidOfLE`.
-/

open Lean

namespace LeanLinter

/-! ## `doc-mislabel` -/

/-- The lower-case words of a docstring's prose, leaving out code spans: a docstring that says
"dual of `Monotone.foo`" names a lemma, it does not call this one monotone. "Increasing" and
"decreasing" count as "monotone" and "antitone" too. -/
def docWords (doc : String) : List String :=
  let prose := (doc.splitOn "`").zipIdx.filter (·.2 % 2 == 0) |>.map (·.1)
  let words := prose.flatMap fun p => (p.split (fun c : Char => !c.isAlpha)).toList.map (·.toString.toLower)
  words.filter (· ≠ "") |>.flatMap fun
    | w@"increasing" | w@"nondecreasing" => [w, "monotone"]
    | w@"decreasing" | w@"nonincreasing" => [w, "antitone"]
    | w => [w]

/-- Families of properties, each member with the constant a conclusion has when it states it. -/
def docFamilies : List (List (String × Name)) :=
  [[("injective", `Function.Injective), ("surjective", `Function.Surjective),
    ("bijective", `Function.Bijective)],
   [("injective", `Set.InjOn), ("surjective", `Set.SurjOn)],
   [("monotone", `Monotone), ("antitone", `Antitone)],
   [("monotone", `MonotoneOn), ("antitone", `AntitoneOn)],
   [("open", `IsOpen), ("closed", `IsClosed)],
   [("continuous", `Continuous), ("differentiable", `Differentiable)]]

def docMislabel (ctx : Ctx) : IO (Array Finding) := do
  let mut out := #[]
  for d in ctx.decls do
    unless d.info.isTheorem && !ctx.isDeprecated d.name do continue
    let some head := (conclusion d.info.type).getAppFn.constName? | continue
    let some doc ← findDocString? ctx.env d.name (includeBuiltin := false) | continue
    let words := docWords doc
    for family in docFamilies do
      let some (actual, _) := family.find? (·.2 == head) | continue
      if words.contains actual then continue
      for (other, _) in family do
        if other != actual && words.contains other then
          out := out.push <| ctx.finding "doc-mislabel" d
            s!"the docstring says \"{other}\" and never \"{actual}\", but the conclusion is `{head}`"
  return out

def docMislabelCheck : Check where
  name := "doc-mislabel"
  summary := "the docstring names one property of a family, the conclusion another"
  run := docMislabel

/-! ## `doc-refs` -/

/-- A word with case, `_`, `!` and `?` dropped, so that `ring_nf!` and the syntax kind `ringNF`
compare equal. -/
def normalizeWord (w : String) : String :=
  String.ofList (w.toList.filter (fun c => c != '_' && c != '!' && c != '?') |>.map Char.toLower)

/-- Everything a backticked name in a docstring can refer to:

* every dot-suffix of every constant, module and option name (`Foo.bar` is reachable as `bar`
  inside `namespace Foo` or after `open Foo`, so `bar` counts as existing);
* every tactic, attribute and command, as `~` followed by the normalized last component of its
  syntax kind (`ring_nf` is the kind `Mathlib.Tactic.RingNF.ringNF`, `simp_rw` the kind
  `tacticSimp_rw__`). -/
def knownNames (env : Environment) : IO (Std.HashSet String) := do
  let addSuffixes (s : Std.HashSet String) (n : Name) : Std.HashSet String :=
    let parts := (userName n).components.map toString
    (List.range parts.length).foldl (fun s i => s.insert (".".intercalate (parts.drop i))) s
  let mut known : Std.HashSet String := {}
  for (n, _) in env.constants.map₁.toList do
    known := addSuffixes known n
  for m in env.header.moduleNames do
    known := addSuffixes known m
    -- a docstring may name a module by a stretch from its middle: `Packed.Product` for
    -- `Foo.Packed.Product.Proof`
    let parts := (userName m).components.map toString
    for i in [0:parts.length] do
      for j in [i + 1:parts.length + 1] do
        known := known.insert (".".intercalate ((parts.drop i).take (j - i)))
  for (n, _) in (← getOptionDecls).toList do
    known := addSuffixes known n
  for a in (← getBuiltinAttributeNames) do
    known := known.insert ("~" ++ normalizeWord (toString a))
  for (kind, _) in (Parser.parserExtension.getState env).kinds.toList do
    let w := normalizeWord (lastString kind)
    known := known.insert ("~" ++ w)
    if w.startsWith "tactic" then known := known.insert ("~" ++ (w.drop 6).toString)
  return known

/-- The backticked spans of a docstring that look like declaration names: identifier characters
only, and at least one `.` or `_` (so `x`, `f` and `n` are left alone). -/
def docReferences (doc : String) : Array String := Id.run do
  let mut out := #[]
  for (span, i) in (doc.splitOn "`").zipIdx do
    if i % 2 == 0 || span.length < 3 || span.length > 80 then continue
    let identChar (c : Char) := c.isAlphanum || "_.'!?".contains c || (c.toNat > 127 && !c.isWhitespace)
    unless span.all identChar && span.any (fun c => c == '.' || c == '_') do continue
    if span.startsWith "." || span.endsWith "." || span.front.isDigit then continue
    out := out.push span
  return out

/-- Does the backticked name `r` refer to something in `known`? Besides names themselves, this
accepts dot notation on a local variable (`f.symm`, `S.g`, `φ.τ₂`), dot notation on a name
(`Finset.univ.sum`), and notation such as `a..b`. -/
def resolves (known : Std.HashSet String) (r : String) : Bool :=
  let r := if r.startsWith "_root_." then (r.drop 7).toString else r
  let parts := r.splitOn "."
  let last := parts.getLast!
  known.contains r || known.contains ("~" ++ normalizeWord r)
    || (r.splitOn "..").length > 1
    || (parts.length > 1 && (parts.head!.length ≤ 3 || parts.head!.front.isLower) && known.contains last)
    || (parts.length > 2 && known.contains (".".intercalate (parts.take 2)) && known.contains last)

/-- The names of the binders in a declaration's type: a docstring may call its own parameters by
name (`width_eq` lets parameterized APIs ...). -/
partial def binderNames (e : Expr) : Std.HashSet String :=
  let rec go (e : Expr) (acc : Std.HashSet String) : Std.HashSet String :=
    match e with
    | .forallE n t b _ => go b (go t (acc.insert (toString n)))
    | .lam n t b _ => go b (go t (acc.insert (toString n)))
    | .mdata _ b => go b acc
    | _ => acc
  go e {}

/-- A docstring mentioning one of the declaration's own parameters, or a keyword the project adds to
the grammar (`float_format`), is not naming a missing declaration. -/
def isLocalOrToken (env : Environment) (locals : Std.HashSet String) (r : String) : Bool :=
  locals.contains r || locals.contains (r.splitOn ".").head!
    || ((Parser.getTokenTable env).find? r).isSome

def docRefs (ctx : Ctx) : IO (Array Finding) := do
  let known ← knownNames ctx.env
  let mut out := #[]
  for d in ctx.decls do
    let some doc ← findDocString? ctx.env d.name (includeBuiltin := false) | continue
    for r in docReferences doc do
      unless resolves known r || isLocalOrToken ctx.env (binderNames d.info.type) r do
        out := out.push <| ctx.finding "doc-refs" d s!"the docstring mentions `{r}`, which does not exist"
  return out

def docRefsCheck : Check where
  name := "doc-refs"
  summary := "the docstring names a declaration that does not exist"
  run := docRefs

end LeanLinter
