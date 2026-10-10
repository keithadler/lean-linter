import LeanLinter.Basic

/-!
# `namespace`: a declaration about a sibling of its namespace's type

`Foo.bar` lives in the namespace of a type `Foo`, but its statement never mentions `Foo` and is
about a *sibling* of `Foo` instead. In Mathlib, three instances in the `CommMonCat` namespace state
that the forgetful functor of `MonCat` creates limits: they were copied from `MonCat` and never
changed, so the `CommMonCat` instances do not exist. In Lean core, `UInt16.toFin_mod` was once
stated for `UInt8`.

## How it decides

Theorems and instances are checked (an instance's type is all it says). Report `Foo.bar` when
`Foo` is a type, the statement mentions neither `Foo` nor anything in its namespace, and it does
mention a type `Bar` that is a sibling of `Foo`:

* *strong* siblings differ only in digits (`UInt8`, `UInt16`) or by one swapped word (`WithTop`,
  `WithBot`), and count on their own;
* *weak* siblings are number types (`Nat`, `Rat`) or differ by words in front (`CommMonCat`,
  `MonCat`), and count only when `Bar.bar` also exists: then `Foo.bar` is a copy of it.

Mathlib files many lemmas in a namespace for organization (a `Rat` lemma about `Nat` helpers, a
`CStarAlgebra` lemma for the weaker `NonUnitalCStarAlgebra`), which is why weak siblings need the
same-named declaration.
-/

open Lean

namespace LeanLinter

/-- Number types, easily mistaken for one another. -/
def numberTypes : List Name :=
  [`Nat, `Int, `Rat, `Real, `Complex, `NNReal, `ENNReal, `EReal, `NNRat, `PNat, `ENat, `ZMod, `Fin,
   `UInt8, `UInt16, `UInt32, `UInt64, `USize, `Int8, `Int16, `Int32, `Int64, `ISize, `Float, `Float32]

/-- Words that turn a type's name into a sibling's when swapped. -/
def siblingSwaps : List (String × String) :=
  [("Top", "Bot"), ("Left", "Right"), ("Upper", "Lower"), ("Add", "Mul"), ("Sup", "Inf"),
   ("Min", "Max"), ("Fst", "Snd")]

/-- `s` without its digits. -/
private def withoutDigits (s : String) : String :=
  String.ofList (s.toList.filter (!·.isDigit))

/-- `a` and `b` differ only in digits, or by swapping one word in `siblingSwaps`. -/
def strongSiblings (a b : Name) : Bool :=
  let sa := toString a
  let sb := toString b
  a != b && (withoutDigits sa == withoutDigits sb
    || siblingSwaps.any fun (x, y) => sa.replace x y == sb || sa.replace y x == sb)

/-- `long` is `short` with capitalized words in front: `CommMonCat` and `MonCat`. -/
private def prefixedBy (long short : String) : Bool :=
  let front := String.ofList (long.toList.take (long.length - short.length))
  long.length > short.length && long.endsWith short && short.length ≥ 3 && short.front.isUpper
    && front.front.isUpper && !front.contains '.'

/-- `a` and `b` are both number types, or one is the other with words in front. -/
def weakSiblings (a b : Name) : Bool :=
  let sa := toString a
  let sb := toString b
  a != b && ((numberTypes.contains a && numberTypes.contains b) || prefixedBy sa sb || prefixedBy sb sa)

def namespaceMismatch (ctx : Ctx) : IO (Array Finding) := do
  let mut out := #[]
  for d in ctx.decls do
    unless (d.info.isTheorem || Meta.isInstanceCore ctx.env d.name) && !ctx.isDeprecated d.name do
      continue
    let ns := (userName d.name).getPrefix
    let some nsInfo := ctx.env.find? ns | continue
    unless isTypeFormer nsInfo do continue
    let used := usedConstants d.info.type
    if used.any fun c => c == ns || ns.isPrefixOf c then continue
    let short := lastString (userName d.name)
    let sibling? := used.find? fun c =>
      (ctx.env.find? c).any isTypeFormer
        && (strongSiblings ns c || (weakSiblings ns c && ctx.env.contains (c.str short)))
    if let some sibling := sibling? then
      out := out.push <| ctx.finding "namespace" d
        s!"in namespace `{ns}`, but the statement is about `{sibling}` and never mentions `{ns}`"
  return out

def namespaceCheck : Check where
  name := "namespace"
  summary := "in the namespace of a type, but stated about a sibling of that type"
  run := namespaceMismatch

end LeanLinter
