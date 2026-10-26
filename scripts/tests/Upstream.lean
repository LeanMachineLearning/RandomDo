import RandomDo.Monad.Notation

open Lean RandomDo.Upstream

namespace UpstreamTests

@[upstream Pure Bind]
def adapted : Nat := 0

run_cmd do
  let env ← getEnv
  unless upstreamAttr.getParam? env `UpstreamTests.adapted == some #[`Pure, `Bind] do
    throwError "Multiple upstream references were not recorded"
  unless upstreamAttr.getParam? env `RDo.randOps == some #[`Lean.Elab.Do.DoOps.default] do
    throwError "Upstream metadata did not survive importing a compiled module"

/-- error: Unknown constant `NoSuchCoreDeclaration` -/
#guard_msgs in
@[upstream NoSuchCoreDeclaration]
def unknownOrigin : Nat := 0

/-- error: Duplicate upstream declarations -/
#guard_msgs in
@[upstream Pure Pure]
def duplicateOrigin : Nat := 0

/--
error: Upstream declaration `MeasurableSpaceMonad` belongs to `RandomDo.Monad.MeasurableSpace`, not Lean core
-/
#guard_msgs in
@[upstream MeasurableSpaceMonad]
def nonCoreOrigin : Nat := 0

end UpstreamTests
