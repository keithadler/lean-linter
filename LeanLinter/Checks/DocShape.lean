import LeanLinter.Basic
import LeanLinter.Checks.Docs

/-!
# `doc-iff`: a docstring that promises an iff the statement does not state

The docstring says "if and only if" (or "iff"), but the statement is not an `↔`. The lemma proves
one direction, or something else, and its docstring describes more than it gives.

Left alone: `a = b` between `Bool`s (how Lean states an `↔` about decidable predicates), a lemma
whose proof is one direction of an iff lemma (`alias ⟨_, card_pair⟩ := card_pair_eq_two_iff`, which
inherits that lemma's docstring), and a docstring that names a lemma ending in `iff` ("see
`foo_iff` for the iff version").
-/

open Lean

namespace LeanLinter

/-! ## `doc-iff` -/

/-- Does the prose of `doc` (outside code spans) say "if and only if" or "iff"? -/
def saysIff (doc : String) : Bool :=
  let prose := ((doc.splitOn "`").zipIdx.filter (·.2 % 2 == 0) |>.map (·.1))
  let text := " ".intercalate (prose.map String.toLower)
  (text.splitOn "if and only if").length > 1
    || (text.splitOn "if, and only if").length > 1
    || (docWords doc).contains "iff"

def docIff (ctx : Ctx) : IO (Array Finding) := do
  let mut out := #[]
  for d in ctx.decls do
    unless d.info.isTheorem && !ctx.isDeprecated d.name do continue
    let c := conclusion d.info.type
    if c.getAppFn.constName? == some ``Iff || mentionsLast d.info.type "Iff" then continue
    -- `a = b` between `Bool`s is how Lean states an `↔` about decidable predicates
    if c.getAppFn.constName? == some ``Eq && (c.getAppArgs[0]?.any (·.isConstOf ``Bool)) then continue
    let some doc ← findDocString? ctx.env d.name (includeBuiltin := false) | continue
    -- a docstring that points at the iff version of this lemma
    let namesIff := ((doc.splitOn "`").zipIdx.filter (·.2 % 2 == 1) |>.map (·.1)).any
      fun span => (span.splitOn "iff").length > 1
    -- one direction of an iff lemma, whose docstring it inherits
    let oneDirection := (d.info.value? (allowOpaque := true)).any fun v =>
      (usedConstants v).any fun c => c == ``Iff.mp || c == ``Iff.mpr
    if saysIff doc && !namesIff && !oneDirection then
      out := out.push <| ctx.finding "doc-iff" d
        "the docstring says \"if and only if\", but the statement is not an `↔`"
  return out

def docIffCheck : Check where
  name := "doc-iff"
  summary := "the docstring says \"if and only if\", but the statement is not an `↔`"
  run := docIff

end LeanLinter
