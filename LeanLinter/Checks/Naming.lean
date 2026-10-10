import LeanLinter.Basic

/-!
# Checks on what a name promises

* `namespace`: `Foo.bar` lives in namespace `Foo`, a type, but its statement never mentions `Foo`
  and is about a sibling of it instead: `UInt16.toFin_mod` stated for `UInt8`, a `WithTop` lemma
  about `WithBot`, an `Int` lemma about `Nat`. Namespaces used only for organization are left alone.
* `name-shape`: a name ending in `_iff` whose conclusion contains no `↔`, or a name promising one
  property of a family (`_injective`) whose conclusion is another (`Function.Surjective`). Words
  after `_of_` describe hypotheses and are not checked.
-/

open Lean

namespace LeanLinter

/-- Types that are easily confused with one another: number systems and their siblings. -/
def numberTypes : List Name :=
  [`Nat, `Int, `Rat, `Real, `Complex, `NNReal, `ENNReal, `EReal, `NNRat, `PNat, `ENat, `ZMod, `Fin,
   `UInt8, `UInt16, `UInt32, `UInt64, `USize, `Int8, `Int16, `Int32, `Int64, `ISize, `Float, `Float32]

/-- `a` and `b` are siblings: they differ only in digits (`UInt8`/`UInt16`), by one swapped word
(`WithTop`/`WithBot`), or are both number types. -/
def siblings (a b : Name) : Bool :=
  let sa := toString a; let sb := toString b
  let strip (s : String) := String.mk (s.toList.filter (!·.isDigit))
  a != b && ((strip sa == strip sb) || (mirrorsOf sa).contains sb
    || (numberTypes.contains a && numberTypes.contains b)
    || variantOf sa sb || variantOf sb sa)
where
  /-- `long` is `short` with capitalized words in front: `CommMonCat` and `MonCat`, `AddGroup` and `Group`. -/
  variantOf (long short : String) : Bool :=
    let pre := String.mk (long.toList.take (long.length - short.length))
    long.length > short.length && long.endsWith short && short.length ≥ 3 && short.front.isUpper
      && pre.front.isUpper && !pre.contains '.'
  mirrorsOf (s : String) : List String :=
    [("Top", "Bot"), ("Left", "Right"), ("Upper", "Lower"), ("Add", "Mul"), ("Sup", "Inf"),
     ("Min", "Max"), ("Fst", "Snd")].foldl (init := []) fun acc (x, y) =>
      acc ++ (if (s.splitOn x).length > 1 then [s.replace x y] else [])
        ++ (if (s.splitOn y).length > 1 then [s.replace y x] else [])

/-- Siblings by digits or a swapped word (`UInt8`/`UInt16`, `WithTop`/`WithBot`): confusable even
without a same-named declaration. -/
def strongSiblings (a b : Name) : Bool :=
  let strip (s : String) := String.mk (s.toList.filter (!·.isDigit))
  (strip (toString a) == strip (toString b) && a != b)
    || (siblings.mirrorsOf (toString a)).contains (toString b)

def namespaceMismatch (ctx : Ctx) : IO (Array Finding) := do
  let mut out := #[]
  for d in ctx.decls do
    -- theorems, and instances (whose type is the whole of what they say)
    unless d.info.isTheorem || Meta.isInstanceCore ctx.env d.name do continue
    if ctx.isDeprecated d.name then continue
    let ns := (userName d.name).getPrefix
    if ns.isAnonymous then continue
    let some nsInfo := ctx.env.find? ns | continue
    unless isTypeFormer nsInfo do continue
    let used := usedConstants d.info.type
    if used.any (fun u => u == ns || ns.isPrefixOf u) then continue
    let short := lastString (userName d.name)
    -- a sibling that differs only by a word in front (`CommMonCat`, `MonCat`) counts only when it has
    -- a declaration of the same name: then this one is a copy of it that kept its statement
    let sibs := used.filter fun u =>
      siblings ns u && (ctx.env.find? u).any isTypeFormer
        && (strongSiblings ns u || ctx.env.contains (u.str short))
    if let some s := sibs[0]? then
      out := out.push <| ctx.finding "namespace" d
        s!"in namespace `{ns}`, but the statement is about `{s}` and never mentions `{ns}`"
  return out

/-- Properties that come in families: a lemma named for one should not conclude another. -/
def propertyFamilies : List (List String) :=
  [["injective", "surjective", "bijective"], ["monotone", "antitone", "strictMono", "strictAnti"]]

/-- Does `e` mention a constant whose last component is `n`? -/
def mentionsLast (e : Expr) (n : String) : Bool :=
  (usedConstants e).any (lastString · == n)

def nameShape (ctx : Ctx) : IO (Array Finding) := do
  let mut out := #[]
  for d in ctx.decls do
    let .thmInfo _ := d.info | continue
    if ctx.isDeprecated d.name then continue
    -- in `foo_of_bar` the words after `of` describe hypotheses
    let tokens := (nameTokens d.name).toList.takeWhile (· != "of")
    let some lastTok := tokens.getLast? | continue
    let c := conclusion d.info.type
    let some head := c.getAppFn.constName? | continue
    -- `Antitone.comp_monotone`: dot notation on the conclusion's own type
    if head == (userName d.name).getPrefix then continue
    let h := lowFirst (lastString head)
    let strict := ["lt", "pos"]; let weak := ["le", "nonneg"]
    if strict.contains lastTok && head == ``LE.le && !mentionsLast c "lt" then
      out := out.push <| ctx.finding "name-shape" d
        s!"the name ends in `_{lastTok}` (strict), but the conclusion is a `≤`"
    else if weak.contains lastTok && head == ``LT.lt then
      out := out.push <| ctx.finding "name-shape" d
        s!"the name ends in `_{lastTok}`, but the conclusion is a strict `<`"
    else if lastTok == "iff" then
      unless head == ``Iff || head == ``Eq || mentionsLast c "Iff" do
        out := out.push <| ctx.finding "name-shape" d
          s!"the name ends in `_iff`, but the conclusion is a `{head}` and contains no `↔`"
    else
      for fam in propertyFamilies do
        unless fam.contains lastTok do continue
        for other in fam do
          if other != lastTok && (h == other || h == other ++ "On") then
            out := out.push <| ctx.finding "name-shape" d
              s!"the name says `{lastTok}`, but the conclusion is `{head}`"
  return out

/-- The lower-case words of a docstring, outside code spans (`Monotone.foo` names a lemma, it
does not describe this one). "increasing" and "decreasing" count as "monotone" and "antitone". -/
def docWords (doc : String) : List String :=
  let prose := (doc.splitOn "`").zipIdx.filter (·.2 % 2 == 0) |>.map (·.1)
  let ws := prose.flatMap fun p => (p.split (fun c => !(c.isAlpha))).toList.map (·.toString.toLower)
  ws.filter (· ≠ "") |>.flatMap fun w =>
    if w == "increasing" || w == "nondecreasing" then [w, "monotone"]
    else if w == "decreasing" || w == "nonincreasing" then [w, "antitone"]
    else [w]

/-- Families of properties that docstrings name in words: a docstring naming one member, about a
statement concluding another, describes some other lemma. -/
def docFamilies : List (List (String × Name)) :=
  [[("injective", `Function.Injective), ("surjective", `Function.Surjective),
    ("bijective", `Function.Bijective)],
   [("monotone", `Monotone), ("antitone", `Antitone)],
   [("open", `IsOpen), ("closed", `IsClosed)],
   [("continuous", `Continuous), ("differentiable", `Differentiable)],
   [("injective", `Set.InjOn), ("surjective", `Set.SurjOn)],
   [("monotone", `MonotoneOn), ("antitone", `AntitoneOn)]]

def docMislabel (ctx : Ctx) : IO (Array Finding) := do
  let mut out := #[]
  for d in ctx.decls do
    let .thmInfo _ := d.info | continue
    if ctx.isDeprecated d.name then continue
    let some doc ← findDocString? ctx.env d.name (includeBuiltin := false) | continue
    let words := docWords doc
    let some head := (conclusion d.info.type).getAppFn.constName? | continue
    for fam in docFamilies do
      let some (actual, _) := fam.find? (·.2 == head) | continue
      if words.contains actual then continue
      for (w, _) in fam do
        if w != actual && words.contains w then
          out := out.push <| ctx.finding "doc-mislabel" d
            s!"the docstring says \"{w}\" and never \"{actual}\", but the conclusion is `{head}`"
  return out

end LeanLinter
