module

public import Test.Metropolis
public meta import Test.Metropolis

set_option linter.style.header false

/-!
# Regression tests for Metropolis chains

Checks for the measure semantics and executable density and log-density samplers.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory NumLean

universe u

variable {m : (α : Type) → [MeasurableSpace α] → Type u} [MeasurableSpaceMonad m]

namespace Test.Metropolis

/-- A symmetric proposal on `Bool` that always proposes the other state. -/
def flip (x : Bool) : m Bool := rdo return !x

example : Metropolis (m := Measure) flip false (fun _ => (1 : ℝ)) 0 =
    Measure.dirac #[false] := by
  change (Measure.dirac _).bind _ = _
  exact Measure.dirac_bind (by fun_prop) _

example : MetropolisLog (m := Measure) flip false (fun _ => (0 : ℝ)) 0 =
    Measure.dirac #[false] := by
  change (Measure.dirac _).bind _ = _
  exact Measure.dirac_bind (by fun_prop) _

run_cmd do
  let samples ← (IO.runRandPCGWith 42
    (Metropolis (m := RandM) flip false (fun _ => (1 : Float)) 0) : IO (Array Bool))
  unless samples == #[false] do
    throwError "zero Metropolis transitions must return just the initial state"
  let samples ← (IO.runRandPCGWith 42
    (MetropolisLog (m := RandM) flip false (fun _ => (0 : Float)) 0) : IO (Array Bool))
  unless samples == #[false] do
    throwError "zero log Metropolis transitions must return just the initial state"
  let expected := #[false, true, false, true]
  let samples ← (IO.runRandPCGWith 42
    (Metropolis (m := RandM) flip false (fun _ => (1 : Float)) 3) : IO (Array Bool))
  unless samples == expected do
    throwError "equal-density Metropolis proposals must always be accepted"
  let samples ← (IO.runRandPCGWith 42
    (MetropolisLog (m := RandM) flip false (fun _ => (0 : Float)) 3) : IO (Array Bool))
  unless samples == expected do
    throwError "equal-log-density Metropolis proposals must always be accepted"

run_cmd do
  let samples ← (IO.runRandPCGWith 42
    (Metropolis (m := RandM) flip false (fun x => if x then (2 : Float) else 1) 1) :
      IO (Array Bool))
  unless samples == #[false, true] do
    throwError "uphill Metropolis proposals must always be accepted"
  let samples ← (IO.runRandPCGWith 42
    (MetropolisLog (m := RandM) flip false (fun x => if x then (1000 : Float) else -1000) 1) :
      IO (Array Bool))
  unless samples == #[false, true] do
    throwError "large uphill log-density differences must be accepted"

run_cmd do
  let expected := #[false, false, false, false]
  let samples ← (IO.runRandPCGWith 42
    (Metropolis (m := RandM) flip false (fun x => if x then (0 : Float) else 1) 3) :
      IO (Array Bool))
  unless samples == expected do
    throwError "zero-density Metropolis proposals must leave the current state unchanged"
  let samples ← (IO.runRandPCGWith 42
    (MetropolisLog (m := RandM) flip false (fun x => if x then -Float.inf else 0) 3) :
      IO (Array Bool))
  unless samples == expected do
    throwError "negative-infinite log-density proposals must leave the current state unchanged"

-- The log form agrees with the density form, even after a shift that would underflow the density.
run_cmd do
  let expected ← (IO.runRandPCGWith 42
    (Metropolis (m := RandM) flip false (fun x => if x then Float.exp (-1) else 1) 40) :
      IO (Array Bool))
  for shift in ([0, -1000] : List Float) do
    let samples ← (IO.runRandPCGWith 42
      (MetropolisLog (m := RandM) flip false (fun x => shift - if x then 1 else 0) 40) :
        IO (Array Bool))
    unless samples == expected do
      throwError "density and log-density Metropolis chains disagree for shift {shift}"

/--
error: expected 0 ≤ p ≤ 1, got NaN
-/
#guard_msgs in
run_cmd do
  let _ ← (IO.runRandPCGWith 42
    (MetropolisLog (m := RandM) flip false (fun x => if x then Float.nan else 0) 1) :
      IO (Array Bool))

end Test.Metropolis

end
