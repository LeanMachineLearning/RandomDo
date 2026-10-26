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

-- The attribute records relationships; the CI exporter enforces its Lean core scope.
@[analogue MeasurableSpaceMonad]
def localOrigin : Nat := 0

run_cmd do
  let env ← getEnv
  unless analogueAttr.getParam? env `AnalogueTests.localOrigin == some #[`MeasurableSpaceMonad] do
    throwError "Analogue metadata should allow declarations outside Lean core"

end AnalogueTests
