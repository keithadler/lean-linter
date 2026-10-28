import Lean

/-!
# Shared machinery

Every check reads one compiled `Environment` and reports `Finding`s about the *target*
declarations: those written by hand in the modules being linted. Declarations Lean generates
(equation lemmas, matchers, recursors, `noConfusion`, auxiliary proofs) are never targets.

This file holds the types the checks share (`Finding`, `Decl`, `Ctx`, `Check`) and the small
helpers they use to read names and statements.
-/

open Lean

/-- `true` for theorems. `ConstantInfo.isTheorem` only exists in newer Lean, and Lean Studio builds
this linter with whatever toolchain the checked project uses, so match the constructor instead. -/
def Lean.ConstantInfo.isThm : ConstantInfo → Bool
  | .thmInfo _ => true
  | _ => false

namespace LeanLinter

/-! ## Findings, declarations and checks -/

/-- One problem found by a check, located at a declaration. -/
structure Finding where
  /-- The name of the check that found it, e.g. `"mislabel"`. -/
  check : String
  /-- The declaration it is about. -/
  decl : Name
  /-- The module that declares it. -/
  module : Name
  /-- The line the declaration starts on. -/
  line : Nat
  /-- One sentence saying what is wrong. -/
  message : String

/-- A hand-written declaration of the target library. -/
structure Decl where
  name : Name
  module : Name
  /-- The line the declaration starts on (every target has a source range). -/
  line : Nat
  info : ConstantInfo
  deriving Inhabited

/-- What every check is given: the whole environment, and the declarations to report on. -/
structure Ctx where
  env : Environment
  decls : Array Decl

/-- A check: a name for the command line, a one-line summary for `--list`, and the check itself. -/
structure Check where
  name : String
  summary : String
  run : Ctx → IO (Array Finding)

/-- A finding about `d`. -/
def Ctx.finding (_ : Ctx) (check : String) (d : Decl) (message : String) : Finding :=
  { check, decl := d.name, module := d.module, line := d.line, message }

/-- Is `n` deprecated? Deprecated declarations are on their way out, so checks skip them. -/
def Ctx.isDeprecated (ctx : Ctx) (n : Name) : Bool :=
  Linter.isDeprecated ctx.env n

/-! ## Names -/

/-- The last component of a name, or `""` if it is not a string. -/
def lastString : Name → String
  | .str _ s => s
  | _ => ""

/-- The name as a user writes it, with any private prefix removed. -/
def userName (n : Name) : Name :=
  privateToUserName n

/-- `s` with its first character in lower case, so that the constant `Injective` matches the word
`injective` in a lemma name. -/
def lowFirst (s : String) : String :=
  match s.toList with
  | c :: cs => String.ofList (c.toLower :: cs)
  | [] => s

/-- The `_`-separated words of a declaration's own name, each with its first letter lowered:
`AntitoneOn.map_bddAbove` gives `#["map", "bddAbove"]`. -/
def nameTokens (n : Name) : Array String :=
  ((lastString (userName n)).splitOn "_").filter (· ≠ "") |>.map lowFirst |>.toArray

/-- Last components that Lean gives to declarations it generates. -/
private def generatedLastComponents : List String :=
  ["eq_def", "eq_unfold", "inj", "injEq", "sizeOf_spec", "induct", "induct_unfolding",
   "mutual_induct", "fun_cases", "splitter", "ctorIdx", "toCtorIdx", "congr_simp"]

/-- Was this name made up by Lean rather than written by a person? True for equation lemmas
(`foo.eq_1`), matchers (`foo.match_1`), auxiliary proofs (`foo.proof_1`), and any name with a
numeric or `_`-prefixed component. -/
def isGeneratedName (n : Name) : Bool :=
  let n := userName n
  let last := lastString n
  let numbered (pre : String) := last.startsWith pre && ((last.drop pre.length).all Char.isDigit)
  generatedLastComponents.contains last || numbered "eq_" || numbered "proof_"
    || last.startsWith "match_"
    || n.components.any fun
      | .str _ s => s.startsWith "_"
      | .num _ _ => true
      | .anonymous => false

/-- The line a declaration starts on, or `none` if Lean recorded no source range for it, as for
most generated declarations. -/
def declLine? (env : Environment) (n : Name) : Option Nat :=
  let r := declRangeExt.find? (level := .exported) env n
    <|> declRangeExt.find? (level := .server) env n
  r.map (·.range.pos.line)

/-! ## Statements -/

/-- What a statement concludes: the type with its `∀` binders (and metadata) stripped. The result
may refer to the binders through loose bound variables. -/
partial def conclusion : Expr → Expr
  | .forallE _ _ b _ => conclusion b
  | .mdata _ e => conclusion e
  | e => e

/-- The constants an expression mentions. -/
def usedConstants (e : Expr) : Array Name :=
  e.getUsedConstants

/-- Does `e` mention a constant whose last component is `n`? -/
def mentionsLast (e : Expr) (n : String) : Bool :=
  (usedConstants e).any (lastString · == n)

/-- A declaration's type with universe parameters renamed by position and metadata removed, so
that two statements differing only in those compare equal. `Expr`'s `==` already ignores the
names and annotations of bound variables. -/
def normalizedType (ci : ConstantInfo) : Expr :=
  let params := ci.levelParams.zipIdx.map fun (_, i) => Level.param (Name.mkSimple s!"u{i}")
  (ci.type.instantiateLevelParams ci.levelParams params).replace fun
    | .mdata _ b => some b
    | _ => none

/-- Is this constant a type former, one whose type ends in `Sort`? -/
def isTypeFormer (ci : ConstantInfo) : Bool :=
  match ci with
  | .inductInfo _ => true
  | _ => (conclusion ci.type).isSort

/-! ## Building the context -/

/-- Is this a declaration Lean generated without a name that says so (recursors, `noConfusion`,
matchers)? -/
def isAuxiliary (env : Environment) (n : Name) : Bool :=
  isAuxRecursor env n || isNoConfusion env n || isRecCore env n || Meta.isMatcherCore env n

/-- The context for linting the modules under `roots`: every declaration in them that a person
wrote, which is to say one with a source range and a name Lean did not make up. -/
def Ctx.build (env : Environment) (roots : Array Name) : Ctx := Id.run do
  let mut decls := #[]
  for mod in env.header.moduleNames, data in env.header.moduleData do
    unless roots.any (·.isPrefixOf mod) do continue
    for n in data.constNames do
      if isGeneratedName n || isAuxiliary env n then continue
      let some line := declLine? env n | continue
      let some info := env.find? n | continue
      decls := decls.push { name := n, module := mod, line, info }
  return { env, decls }

end LeanLinter
