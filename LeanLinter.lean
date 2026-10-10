import LeanLinter.Basic
import LeanLinter.Checks.Mislabel
import LeanLinter.Checks.Naming
import LeanLinter.Checks.Docs
import LeanLinter.Checks.Redundancy

open Lean

namespace LeanLinter

/-- Every check, by name, in the order they run. -/
def allChecks : List (String × (Ctx → IO (Array Finding))) :=
  [("mislabel", mislabel), ("namespace", namespaceMismatch), ("name-shape", nameShape), ("doc-mislabel", docMislabel),
   ("doc-refs", docRefs), ("deprecation", deprecation), ("duplicate", (duplicates · false)),
   ("duplicate-sym", (duplicates · true)), ("duplicate-instance", duplicateInstances),
   ("dead-private", deadPrivate)]

end LeanLinter
