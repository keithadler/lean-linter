import LeanLinter.Basic
import LeanLinter.Checks.Mislabel
import LeanLinter.Checks.Namespace
import LeanLinter.Checks.NameShape
import LeanLinter.Checks.Docs
import LeanLinter.Checks.Deprecation
import LeanLinter.Checks.Duplicates
import LeanLinter.Checks.DeadPrivate
import LeanLinter.Checks.Operations
import LeanLinter.Checks.DocShape
import LeanLinter.Checks.Vacuous
import LeanLinter.Checks.Universe
import LeanLinter.Checks.Trust
import LeanLinter.Checks.Diamond

/-!
# lean-linter

Linters that read a compiled Lean environment and report what the type checker cannot see:
names and docstrings that disagree with statements, references and deprecations that lead
nowhere, things stated twice, and private code nothing uses. See `README.md`.
-/

namespace LeanLinter

/-- The version of lean-linter. -/
def version : String := "0.2.0"

/-- Every check, in the order they run and are reported. -/
def allChecks : List Check :=
  [mislabelCheck, namespaceCheck, nameShapeCheck, docMislabelCheck, docRefsCheck, deprecationCheck,
   duplicateCheck, duplicateSymCheck, duplicateInstanceCheck, deadPrivateCheck, opMismatchCheck,
   docIffCheck, vacuousCheck, universeCheck, trustCheck, diamondCheck]

end LeanLinter
