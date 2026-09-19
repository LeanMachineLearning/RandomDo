/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import RandomDo
public import LeanMachineLearning.SequentialLearning.Algorithms.RoundRobin
public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg

/-!
# A Gaussian bandit, as an `rdo` program

`K` arms; pulling arm `a` returns a reward drawn from `𝒩(μ a, σ2)`. A bandit algorithm chooses the
arm to pull from what it has seen so far. The algorithms here only need a summary of it, a
`State`: how many times each arm was pulled, the sum of the rewards each arm returned, and the last
arm pulled. One round of interaction is `banditStep`, and `banditRun n` plays `n` rounds.

The programs are polymorphic in the monad and in the scalars, as those of
`RandomDo.Tactic.Computable.Polymorphic`: read at `Measure` and `ℝ`, they are what
`Bandits.Theory` proves things about; run at `RandM` and `Float`, they sample.

The two algorithms, `etcArm` (explore-then-commit) and `ucbArm` (upper confidence bound), mirror
the definitions of `Bandits.ETC.nextArm` and `Bandits.UCB.nextArm` in LeanMachineLearning, with the
statistics of the history in place of sums over it.

## Main definitions

* `RDoBandit.HasArgmax`: scalars in which a tuple has an index of its maximum.
* `RDoBandit.State`, `RDoBandit.State.update`: what the algorithms keep of the history.
* `RDoBandit.etcArm`, `RDoBandit.ucbArm`: the arm the two algorithms pull.
* `RDoBandit.banditStep`, `RDoBandit.banditRun`: one round, and `n` rounds, of interaction.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning MeasurableSpacePure

/-- A typeclass for scalars in which a nonempty tuple has an index of its maximum. -/
class RDoBandit.HasArgmax (R : Type) where
  /-- An index at which the tuple is maximal. -/
  argmax {K : ℕ} [NeZero K] : (Fin K → R) → Fin K

namespace RDoBandit

/-- At `ℝ`, the `argmax` of LeanMachineLearning: some index at which the tuple is maximal. -/
noncomputable instance : HasArgmax ℝ := ⟨fun f ↦ argmax f⟩

/-- At `Float`, the first index at which the tuple is maximal. It agrees with the instance at `ℝ`
when the maximum is attained once. -/
instance : HasArgmax Float where
  argmax {K} _ f := (List.finRange K).foldl (fun best a ↦ if f best < f a then a else best) 0

/-- What a bandit algorithm keeps of the history: the number of pulls of each arm, the sum of the
rewards each arm returned, and the last arm pulled (arm `0` before the first round). The first two
are arrays, so that updating them in a long run stays cheap. -/
abbrev State (K : ℕ) (R : Type) := Vector ℕ K × Vector R K × Fin K

variable {K : ℕ} [NeZero K] {R : Type}

/-- The state before the first round. -/
def State.init [Zero R] : State K R := (Vector.replicate K 0, Vector.replicate K 0, 0)

/-- The state after pulling arm `a` and receiving reward `r`. -/
def State.update [Add R] (s : State K R) (a : Fin K) (r : R) : State K R :=
  (s.1.set a (s.1[a] + 1), s.2.1.set a (s.2.1[a] + r), a)

/-- Arm `n % K`: pulling the arms in turn. This is `RoundRobin.nextAction` of LeanMachineLearning,
which is not compiled there. -/
def roundRobin (K : ℕ) [NeZero K] (n : ℕ) : Fin K := ⟨n % K, Nat.mod_lt _ (NeZero.pos K)⟩

variable [Div R] [NatCast R] [HasArgmax R]

/-- **Explore-then-commit** with `m` pulls of each arm: the arm pulled at time `n`. Arms are
pulled in turn for the first `K * m` rounds; at round `K * m` the algorithm commits to the arm with
the best empirical mean, and pulls it from then on. -/
def etcArm (m : ℕ) (n : ℕ) (s : State K R) : Fin K :=
  if n < K * m then roundRobin K n
  else if n = K * m then HasArgmax.argmax fun a ↦ s.2.1[a] / (s.1[a] : R)
  else s.2.2

/-- **UCB** with exploration parameter `c`: the arm pulled at time `n`. Arms are pulled in turn for
the first `K` rounds; afterwards the algorithm pulls the arm maximizing the empirical mean plus
`√(2 c log (n + 1) / N)`, where `N` is the number of pulls of the arm. -/
def ucbArm [Add R] [Mul R] [One R] [OfNat R 2] [HasLog R] [HasSqrt R] (c : R) (n : ℕ)
    (s : State K R) : Fin K :=
  if n < K then roundRobin K n
  else HasArgmax.argmax fun a ↦
    s.2.1[a] / (s.1[a] : R) + HasSqrt.sqrt (2 * c * HasLog.log ((n : R) + 1) / (s.1[a] : R))

universe v

variable {m : (α : Type) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
  [Zero R] [Add R] [MeasurableSpace R] {V : Type} [HasGaussian m R V R]

/-- **One round.** The algorithm `arm` chooses an arm from the state, the arm returns a reward drawn
from `𝒩(μ a, σ2)`, and the state records it. -/
def banditStep (arm : ℕ → State K R → Fin K) (μ : Fin K → R) (σ2 : V) (n : ℕ) (s : State K R) :
    m (State K R) := rdo
  let a := arm n s
  let r ← HasGaussian.gaussian (m := m) (μ a) σ2
  return s.update a r

/-- **`n` rounds**, from the initial state. -/
def banditRun (arm : ℕ → State K R → Fin K) (μ : Fin K → R) (σ2 : V) : ℕ → m (State K R)
  | 0 => mPure State.init
  | n + 1 => rdo
    let s ← banditRun arm μ σ2 n
    let s' ← banditStep (m := m) arm μ σ2 n s
    return s'

end RDoBandit
