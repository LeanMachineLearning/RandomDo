module

public import RandomDo

set_option linter.style.header false

/-!
# Polymorphic Metropolis chains

The density and log-density forms of Metropolis, interpreted as measures or executable samplers.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory NumLean

universe u

variable {m : (α : Type) → [MeasurableSpace α] → Type u} [MeasurableSpaceMonad m]

variable {Ω R : Type} [MeasurableSpace Ω] [Scalar R]

def Metropolis [HasBernoulli m R] (g : Ω → m Ω) (x₀ : Ω) (f : Ω → R) (n : ℕ) : m (Array Ω) := rdo
  let mut x := x₀
  let mut samples : Array Ω := #[x₀]
  for _ in List.range n rdo
    let x' ← g x
    let α := f x' / f x
    let accept ← HasBernoulli.bernoulli (m := m) α
    if accept then
      x := x'
    samples := samples.push x
  return samples

def MetropolisLog [HasBernoulli m R] [HasExp R] [LT R] [DecidableLT R]
    (g : Ω → m Ω) (x₀ : Ω) (logf : Ω → R) (n : ℕ) : m (Array Ω) := rdo
  let mut x := x₀
  let mut logfx := logf x₀
  let mut samples : Array Ω := #[x₀]
  for _ in List.range n rdo
    let x' ← g x
    let logfx' := logf x'
    let logα := logfx' - logfx
    let α : R := if 0 < logα then 1 else HasExp.exp logα
    let accept ← HasBernoulli.bernoulli (m := m) α
    if accept then
      x := x'
      logfx := logfx'
    samples := samples.push x
  return samples

end
