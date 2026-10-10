import Lean

/-!
# Shared machinery for the checks

A check reads a whole environment and reports `Finding`s about the declarations of the target
library: the ones written by hand in its modules, not the ones Lean generates (equation lemmas,
matchers, recursors, `noConfusion`, ...).
-/

open Lean

namespace LeanLinter

/-- One problem found by a check. -/
structure Finding where
  check : String
  decl : Name
  module : Name
  line : Nat
  message : String

/-- A hand-written declaration of the target library. -/
structure Decl where
  name : Name
  module : Name
  line : Nat
  info : ConstantInfo
  deriving Inhabited

/-- What every check gets: the environment and the declarations it is asked about. -/
structure Ctx where
  env : Environment
  decls : Array Decl
  moduleOf : Std.HashMap Name Name

/-- The last component of a name, if it is a string. -/
def lastString : Name → String
  | .str _ s => s
  | _ => ""

/-- The name a user writes for a declaration, with any private prefix taken off. -/
def userName (n : Name) : Name := privateToUserName n

/-- Lower-case the first character, so that `Injective` in a constant matches `injective` in a lemma name. -/
def lowFirst (s : String) : String :=
  match s.toList with
  | c :: cs => String.mk (c.toLower :: cs)
  | [] => s

/-- The `_`-separated pieces of a declaration's own name, first letters lowered. -/
def nameTokens (n : Name) : Array String :=
  ((lastString (userName n)).splitOn "_").filter (· ≠ "") |>.map lowFirst |>.toArray

private def generatedSuffixes : List String :=
  ["eq_def", "eq_unfold", "inj", "injEq", "sizeOf_spec", "induct", "induct_unfolding",
   "mutual_induct", "fun_cases", "splitter", "ctorIdx", "toCtorIdx", "congr_simp", "proof_1"]

/-- Names Lean makes up: `_`-prefixed or numeric components, equation lemmas, and the like. -/
def isGeneratedName (n : Name) : Bool :=
  let n := userName n
  let last := lastString n
  generatedSuffixes.contains last || (last.startsWith "eq_" && (last.drop 3).all Char.isDigit)
    || (last.startsWith "match_" ) || (last.startsWith "proof_")
    || n.components.any fun c => match c with
      | .str _ s => s.startsWith "_"
      | .num _ _ => true
      | .anonymous => false

/-- The line a declaration starts on, or `none` if Lean recorded no source range for it. -/
def declLine? (env : Environment) (n : Name) : Option Nat :=
  let r := declRangeExt.find? (level := .exported) env n <|> declRangeExt.find? (level := .server) env n
  r.map (·.range.pos.line)

/-- `forall` binders stripped off; the result may have loose bound variables. -/
partial def conclusion : Expr → Expr
  | .forallE _ _ b _ => conclusion b
  | .mdata _ e => conclusion e
  | e => e

/-- The type with universe parameters renamed by position and metadata removed, so that two
statements that differ only in those compare equal (binder names are already ignored by `==`). -/
def normalizedType (ci : ConstantInfo) : Expr :=
  let ls := ci.levelParams.zipIdx.map fun (_, i) => Level.param (Name.mkSimple s!"u{i}")
  let t := ci.type.instantiateLevelParams ci.levelParams ls
  t.replace fun e => match e with
    | .mdata _ b => some b
    | _ => none

/-- Is this constant a type former (its type ends in `Sort`)? -/
def isTypeFormer (ci : ConstantInfo) : Bool :=
  match ci with
  | .inductInfo _ => true
  | _ => (conclusion ci.type).isSort

/-- Constants an expression mentions. -/
def usedConstants (e : Expr) : Array Name := e.getUsedConstants

/-- Build the context: every hand-written declaration whose module is under one of `roots`. -/
def Ctx.build (env : Environment) (roots : Array Name) : IO Ctx := do
  let mut decls := #[]
  let mut moduleOf : Std.HashMap Name Name := {}
  let names := env.header.moduleNames
  for i in [0:names.size] do
    let mod := names[i]!
    let data := env.header.moduleData[i]!
    for n in data.constNames do
      moduleOf := moduleOf.insert n mod
    unless roots.any (·.isPrefixOf mod) do continue
    for n in data.constNames do
      if isGeneratedName n then continue
      if isAuxRecursor env n || isNoConfusion env n || isRecCore env n || Meta.isMatcherCore env n then
        continue
      let some line := declLine? env n | continue
      let some ci := env.find? n | continue
      decls := decls.push { name := n, module := mod, line, info := ci }
  return { env, decls, moduleOf }

def Ctx.finding (ctx : Ctx) (check : String) (d : Decl) (message : String) : Finding :=
  { check, decl := d.name, module := d.module, line := d.line, message }

def Ctx.isDeprecated (ctx : Ctx) (n : Name) : Bool := Linter.isDeprecated ctx.env n

end LeanLinter
