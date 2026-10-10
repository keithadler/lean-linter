import LeanLinter.Basic

/-!
# Checks on references that can rot

* `doc-refs`: a docstring names a declaration in backticks that does not exist, usually because it
  was renamed or deleted and the docstring was not updated. Only names that look like declaration
  names are checked (they contain `.` or `_`); a name counts as existing if any constant, module,
  token or option ends with it, so references through `open` namespaces are not reported.
* `deprecation`: a deprecated alias points to a declaration that does not exist, or to one that is
  itself deprecated, so users following the hint land on another deprecation.
-/

open Lean

namespace LeanLinter

/-- A word with case, `_`, `!` and `?` dropped, so that `ring_nf!` matches the syntax kind `ringNF`. -/
def normalizeWord (w : String) : String :=
  String.mk (w.toList.filter (fun c => c != '_' && c != '!' && c != '?') |>.map Char.toLower)

/-- Every dot-suffix of every constant and module name, plus syntax kinds and option names. -/
def knownSuffixes (env : Environment) : IO (Std.HashSet String) := do
  let mut s : Std.HashSet String := {}
  let addAll (s : Std.HashSet String) (n : Name) : Std.HashSet String := Id.run do
    let comps := (userName n).components.map toString
    let mut s := s
    for i in [0:comps.length] do
      s := s.insert (".".intercalate (comps.drop i))
    return s
  for (n, _) in env.constants.map₁.toList do
    s := addAll s n
  for m in env.header.moduleNames do
    s := addAll s m
  -- tactics, attributes and commands, by the last component of their syntax kind, normalized
  for (k, _) in (Parser.parserExtension.getState env).kinds.toList do
    let w := normalizeWord (lastString k)
    s := s.insert ("~" ++ w)
    -- `tacticSimp_rw__`, `tacticInfer_instance`: kinds generated from the syntax
    if w.startsWith "tactic" then s := s.insert ("~" ++ (w.drop 6).toString)
  for (n, _) in (← getOptionDecls).toList do
    s := addAll s n
  return s

/-- Backticked spans of a docstring that look like declaration names. -/
def docNames (doc : String) : Array String := Id.run do
  let parts := doc.splitOn "`"
  let mut out := #[]
  for i in [0:parts.length] do
    if i % 2 == 0 then continue
    let p := parts[i]!
    if p.length < 3 || p.length > 80 then continue
    unless p.any (fun c => c == '.' || c == '_') do continue
    unless p.all (fun c => c.isAlphanum || c == '_' || c == '.' || c == '\'' || c == '!' || c == '?'
        || (c.toNat > 127 && !c.isWhitespace)) do continue
    if p.startsWith "." || p.endsWith "." || p.front.isDigit then continue
    out := out.push p
  return out

def docRefs (ctx : Ctx) : IO (Array Finding) := do
  let known ← knownSuffixes ctx.env
  let mut out := #[]
  for d in ctx.decls do
    let some doc ← findDocString? ctx.env d.name (includeBuiltin := false) | continue
    for r in docNames doc do
      let r' := if r.startsWith "_root_." then (r.drop 7).toString else r
      if known.contains r' || known.contains ("~" ++ normalizeWord r') then continue
      -- `a..b` and the like are notation, not names
      if (r'.splitOn "..").length > 1 then continue
      -- `f.symm`, `S.g`, `φ.τ₂`: a field or dot-notation call on a short local name
      let comps := r'.splitOn "."
      if comps.length > 1 && comps.head!.length ≤ 3 && known.contains comps.getLast! then
        continue
      -- `Finset.univ.sum`: dot notation on a name that exists
      if comps.length > 2 && known.contains (".".intercalate (comps.take 2)) && known.contains comps.getLast! then
        continue
      if comps.length > 1 && comps.head!.front.isLower && known.contains (".".intercalate comps.tail) then
        continue
      out := out.push <| ctx.finding "doc-refs" d s!"the docstring mentions `{r}`, which does not exist"
  return out

def deprecation (ctx : Ctx) : IO (Array Finding) := do
  let mut out := #[]
  for d in ctx.decls do
    let some e := Linter.deprecatedAttr.getParam? ctx.env d.name | continue
    let some new := e.newName? | continue
    if !ctx.env.contains new then
      out := out.push <| ctx.finding "deprecation" d s!"deprecated in favor of `{new}`, which does not exist"
    else if ctx.isDeprecated new then
      out := out.push <| ctx.finding "deprecation" d
        s!"deprecated in favor of `{new}`, which is itself deprecated"
  return out

end LeanLinter
