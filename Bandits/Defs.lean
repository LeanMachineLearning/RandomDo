/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import RandomDo
public import LeanMachineLearning.SequentialLearning.Algorithms.RoundRobin
public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg
public import Mathlib.Probability.Distributions.Uniform

/-!
# A Gaussian bandit, as an `rdo` program

`K` arms; pulling arm `a` returns a reward drawn from `𝒩(μ a, σ2)`. A bandit algorithm chooses the
arm to pull from what it has seen so far. The algorithms here only need a summary of it, a
`State`: how many times each arm was pulled, the sum of the rewards each arm returned, and the last
arm pulled. One round of interaction is `banditStep`, and `banditRun n` plays `n` rounds.

The programs are polymorphic in the monad and in the scalars, as those of
`RandomDo.Tactic.Computable.Polymorphic`: read at `Measure` and `ℝ`, they are what
`Bandits.Theory` and `Bandits.EpsGreedy` prove things about; run at `RandM` and `Float`, they
sample. To run them and draw the regret against the bounds, from the root of the repository:

```
lake exe bandits                  # 300 seeds × 5000 rounds; writes bandit_output/
python3 scripts/bandit_plot.py    # checks them against numpy, draws bandit_output/*.png
```

The two algorithms, `etcArm` (explore-then-commit) and `ucbArm` (upper confidence bound), mirror
the definitions of `Bandits.ETC.nextArm` and `Bandits.UCB.nextArm` in LeanMachineLearning, with the
statistics of the history in place of sums over it. A third, `epsGreedyArm` (ε-greedy), is
randomized: it is itself an `rdo` program, played by `banditStepRand` and `banditRunRand`.

## Main definitions

* `RDoBandit.HasArgmax`: scalars in which a tuple has an index of its maximum.
* `RDoBandit.State`, `RDoBandit.State.update`: what the algorithms keep of the history.
* `RDoBandit.etcArm`, `RDoBandit.ucbArm`: the arm the two algorithms pull.
* `RDoBandit.banditStep`, `RDoBandit.banditRun`: one round, and `n` rounds, of interaction.
* `RDoBandit.HasUniformFin`, `RDoBandit.epsGreedyArm`: ε-greedy, drawing its arm.
* `RDoBandit.banditStepRand`, `RDoBandit.banditRunRand`: the interaction for an algorithm that
  draws its arm.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning MeasurableSpacePure

universe v

/-- A typeclass for monads that can draw an arm uniformly. -/
class RDoBandit.HasUniformFin (m : (α : Type) → [MeasurableSpace α] → Type v) where
  /-- Draw an element of `Fin K` uniformly. -/
  uniformFin (K : ℕ) [NeZero K] : m (Fin K)

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

noncomputable instance : HasUniformFin Measure where
  uniformFin K _ := (PMF.uniformOfFintype (Fin K)).toMeasure

instance (K : ℕ) [NeZero K] :
    IsProbabilityMeasure (HasUniformFin.uniformFin (m := Measure) K) := by
  change IsProbabilityMeasure (PMF.uniformOfFintype (Fin K)).toMeasure
  infer_instance

/-- The uniform draw of `NumLean`, as numpy's `Generator.integers`. -/
instance : HasUniformFin RandM where
  uniformFin K _ := show NumLean.RandPCG IO (Fin K) from do
    return ⟨(← NumLean.randInt K).toNat % K, Nat.mod_lt _ (NeZero.pos K)⟩

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

/-- The first arm never pulled, if any. -/
def firstUnpulled (s : State K R) : Option (Fin K) :=
  (List.finRange K).find? fun a ↦ s.1[a] == 0

/-- The greedy arm: the first arm never pulled if there is one, and otherwise the arm with the best
empirical mean. Pulling the unpulled arms first keeps the empirical means defined when they are
compared. -/
def greedyArm (s : State K R) : Fin K :=
  match firstUnpulled s with
  | some a => a
  | none => HasArgmax.argmax fun a ↦ s.2.1[a] / (s.1[a] : R)

variable {m : (α : Type) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
  [Zero R] [Add R] [MeasurableSpace R] {V : Type} [HasGaussian m R V R]

/-- **One round.** The algorithm `arm` chooses an arm from the state, the arm returns a reward drawn
from `𝒩(μ a, σ2)`, and the state records it. -/
def banditStep (arm : ℕ → State K R → Fin K) (μ : Fin K → R) (σ2 : V) (n : ℕ) (s : State K R) :
    m (State K R) := rdo
  let a := arm n s
  let r ← HasGaussian.gaussian (m := m) (μ a) σ2
  return s.update a r

/-- **ε-greedy**, drawing the arm it pulls: a coin of bias `ε`; on heads an arm drawn uniformly, on
tails the greedy arm. Both draws are made every round. -/
def epsGreedyArm [HasBernoulli m R] [HasUniformFin m] (ε : R) (_n : ℕ) (s : State K R) :
    m (Fin K) := rdo
  let explore ← HasBernoulli.bernoulli (m := m) ε
  let u ← HasUniformFin.uniformFin (m := m) K
  return if explore then u else greedyArm s

/-- **`n` rounds**, from the initial state. -/
def banditRun (arm : ℕ → State K R → Fin K) (μ : Fin K → R) (σ2 : V) : ℕ → m (State K R)
  | 0 => mPure State.init
  | n + 1 => rdo
    let s ← banditRun arm μ σ2 n
    let s' ← banditStep (m := m) arm μ σ2 n s
    return s'

/-- **One round**, for an algorithm that draws its arm: the program `arm` draws the arm from the
state, the arm returns a reward drawn from `𝒩(μ a, σ2)`, and the state records it. -/
def banditStepRand (arm : ℕ → State K R → m (Fin K)) (μ : Fin K → R) (σ2 : V) (n : ℕ)
    (s : State K R) : m (State K R) := rdo
  let a ← arm n s
  let r ← HasGaussian.gaussian (m := m) (μ a) σ2
  return s.update a r

/-- **`n` rounds**, for an algorithm that draws its arm. -/
def banditRunRand (arm : ℕ → State K R → m (Fin K)) (μ : Fin K → R) (σ2 : V) :
    ℕ → m (State K R)
  | 0 => mPure State.init
  | n + 1 => rdo
    let s ← banditRunRand arm μ σ2 n
    let s' ← banditStepRand (m := m) arm μ σ2 n s
    return s'

end RDoBandit
