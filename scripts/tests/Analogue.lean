import RandomDo.Monad.Notation

open Lean RandomDo.Analogue

namespace AnalogueTests

@[analogue Pure Bind]
def adapted : Nat := 0

run_cmd do
  let env ← getEnv
  unless analogueAttr.getParam? env `AnalogueTests.adapted == some #[`Pure, `Bind] do
    throwError "Multiple analogue references were not recorded"
  unless analogueAttr.getParam? env `RDo.randOps == some #[`Lean.Elab.Do.DoOps.default] do
    throwError "Analogue metadata did not survive importing a compiled module"

/-- error: Unknown constant `NoSuchCoreDeclaration` -/
#guard_msgs in
@[analogue NoSuchCoreDeclaration]
def unknownOrigin : Nat := 0

/-- error: Duplicate analogue declarations -/
#guard_msgs in
@[analogue Pure Pure]
def duplicateOrigin : Nat := 0

/--
error: Analogue declaration `MeasurableSpaceMonad` belongs to `RandomDo.Monad.MeasurableSpace`, not Lean core
-/
#guard_msgs in
@[analogue MeasurableSpaceMonad]
def nonCoreOrigin : Nat := 0

end AnalogueTests
