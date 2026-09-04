/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import RandomDo.Probability.Tactic
public import RandomDo.Tactic.Elab
public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg

set_option linter.style.header false

/-!
# Thompson sampling as random variables

`thompson`, defined below, is an `rdo` program: a loop folding the history into
per-arm pull counts `N` and reward sums `S`, a loop drawing one Gaussian posterior sample per arm
into a vector `θ`, and `return argmax θ`. As a measure on `Fin K` it has no random variables —
there is no `θ` to talk about. This file gives it some.

The trace `rdo_trace` finds has one coordinate per stage:

* `ω.1 : (Fin K → ℝ) × (Fin K → ℝ)` — the sufficient statistics `(N, S)` read off the history;
* `ω.2 : Fin K → ℝ` — the vector `θ` of posterior samples;

with readout `argmax ω.2`. Peeling it gives the three statements of `hasLaw_thompson`: the
statistics have the law of the folding stage, `θ` given them has the law of the sampling stage —
so `θ` depends on the history *only through* `(N, S)` — and the action Thompson sampling plays is
`argmax θ`.

Both loops are traced coarsely, as one draw each: see `notes/TRACE_SEMANTICS.md` for what
per-iteration granularity inside the sampling loop would take.

## Main definitions

* `RDo.Thompson.stats`, `RDo.Thompson.sample`: the two stages, as `rdo` programs of their own.
* `RDo.Thompson.statsK`, `RDo.Thompson.sampleK`: the same, as Markov kernels.
* `RDo.Thompson.traceMeasure`: the joint law of the two stages given the history.

## Main results

* `RDo.Thompson.thompson_eq`: `thompson` *is* `stats`, then `sample`, then `argmax`.
* `RDo.Thompson.hasTrace_thompson`: the trace of `thompson`.
* `RDo.Thompson.hasLaw_thompson`: the three statements above.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MeasurableSpacePure MeasurableSpaceBind

noncomputable section

namespace RDo.Thompson

variable {K n : ℕ}

attribute[fun_prop] Measurable.ite

/-! ## The two stages -/

/-- Stage one: fold the history into the per-arm pull counts `N` (started at one) and reward
sums `S`. It draws nothing. -/
def stats (hist : Vector (Fin K × ℝ) n) : Measure ((Fin K → ℝ) × (Fin K → ℝ)) := rdo
  let mut N : Fin K → ℝ := fun _ ↦ 1
  let mut S : Fin K → ℝ := fun _ ↦ 0
  for (a, r) in hist rdo
    N := fun j ↦ if j = a then N j + 1 else N j
    S := fun j ↦ if j = a then S j + r else S j
  return (N, S)

instance : IsMarkov (stats (K := K) (n := n)) := by is_markov

/-- Stage two: one Gaussian posterior draw per arm, with mean and variance determined by the
statistics, collected into the vector `θ`. -/
def sample (NS : (Fin K → ℝ) × (Fin K → ℝ)) : Measure (Fin K → ℝ) := rdo
  let mut θ : Fin K → ℝ := fun _ ↦ 0
  for j in List.finRange K rdo
    let z ← gaussianReal (NS.2 j / NS.1 j) (Real.toNNReal (1 / NS.1 j))
    θ := fun k ↦ if k = j then z else θ k
  return θ

instance : IsMarkov (sample (K := K)) := by is_markov

/-- Stage one as a Markov kernel from the history. -/
def statsK : Kernel (Vector (Fin K × ℝ) n) ((Fin K → ℝ) × (Fin K → ℝ)) :=
  markovKernel stats inferInstance

instance : IsMarkovKernel (statsK (K := K) (n := n)) := by unfold statsK; infer_instance

/-- Stage two as a Markov kernel from the statistics. -/
def sampleK : Kernel ((Fin K → ℝ) × (Fin K → ℝ)) (Fin K → ℝ) := markovKernel sample inferInstance

instance : IsMarkovKernel (sampleK (K := K)) := by unfold sampleK; infer_instance

@[simp] lemma statsK_apply (hist : Vector (Fin K × ℝ) n) : statsK hist = stats hist := rfl

@[simp] lemma sampleK_apply (NS : (Fin K → ℝ) × (Fin K → ℝ)) : sampleK NS = sample NS := rfl

def thompson {K n : ℕ} (hK : 0 < K) (hist : Vector (Fin K × ℝ) n) :
    Measure (Fin K) := rdo
  let mut N : Fin K → ℝ := fun _ ↦ 1
  let mut S : Fin K → ℝ := fun _ ↦ 0
  for (a, r) in hist rdo
    N := fun j ↦ if j = a then N j + 1 else N j
    S := fun j ↦ if j = a then S j + r else S j
  let mut θ : Fin K → ℝ := fun _ ↦ 0
  for j in List.finRange K rdo
    let z ← gaussianReal (S j / N j) (Real.toNNReal (1 / N j))
    θ := fun k ↦ if k = j then z else θ k
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  return argmax θ

/-- `thompson` is exactly: fold the history into `(N, S)`, draw the posterior sample `θ` given
them, play `argmax θ`. Both sides elaborate to the same two loops; all that separates them is the
`return` at the end of each stage. -/
theorem thompson_eq (hK : 0 < K) (hist : Vector (Fin K × ℝ) n) :
    haveI : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
    thompson hK hist = stats hist >>=ₘ fun NS ↦ sample NS >>=ₘ fun θ ↦ mPure (argmax θ) := by
  unfold thompson stats sample
  simp only [Prod.mk.eta, mBind_mPure]

/-! ## The trace -/

/-- The joint law of the two stages: the statistics, then the posterior sample given them. -/
def traceMeasure (hist : Vector (Fin K × ℝ) n) :
    Measure (((Fin K → ℝ) × (Fin K → ℝ)) × (Fin K → ℝ)) :=
  (statsK ⊗ₖ sampleK.comap Prod.snd measurable_snd) hist

instance (hist : Vector (Fin K × ℝ) n) : IsProbabilityMeasure (traceMeasure hist) := by
  unfold traceMeasure
  infer_instance

/-- **The trace of `thompson`.** Found by `rdo_trace`, which stops at `stats` and at `sample`
because each carries an `IsMarkov` instance: that is the granularity knob, and it is what keeps
the trace readable rather than exposing the two raw loops. -/
theorem hasTrace_thompson (hK : 0 < K) :
    haveI : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
    HasTrace (thompson (n := n) hK) (statsK ⊗ₖ sampleK.comap Prod.snd measurable_snd)
      (fun p : Vector (Fin K × ℝ) n × (((Fin K → ℝ) × (Fin K → ℝ)) × (Fin K → ℝ)) ↦
        argmax p.2.2) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  rdo_trace (fun hist : Vector (Fin K × ℝ) n ↦
    stats hist >>=ₘ fun NS ↦ sample NS >>=ₘ fun θ ↦ mPure (argmax θ)) with h
  exact h.congr fun hist ↦ thompson_eq hK hist

/-! ## The random variables -/

/-- **Thompson sampling, as random variables.** On the trace space, writing `NS := ω.1` for the
sufficient statistics and `θ := ω.2` for the vector of posterior samples:

* `NS` has the law of the folding stage;
* `θ` has, given `NS`, the law of the sampling stage — so `θ` depends on the history only through
  `NS`, which is the whole content of "Thompson sampling is a function of the sufficient
  statistics";
* the action the algorithm plays is `argmax θ`.

Everything below the `rdo_trace` line is produced by `rdo_peel`. -/
theorem hasLaw_thompson (hK : 0 < K) (hist : Vector (Fin K × ℝ) n) :
    haveI : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
    HasLaw (fun ω ↦ ω.1) (stats hist) (traceMeasure hist)
      ∧ HasCondDistrib (fun ω ↦ ω.2) (fun ω ↦ ω.1) sampleK (traceMeasure hist)
      ∧ HasLaw (fun ω ↦ argmax ω.2) (thompson hK hist) (traceMeasure hist) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  have h := hasTrace_thompson (n := n) hK
  rdo_peel h hist with hNS hθ hout
  exact ⟨hNS, hθ, hout⟩

/-! ## Recording a value the program only computes

The trace above has a coordinate for each of the two *stages*, so `N` and `S` can only be spoken
about together, as `ω.1`. They are not draws — the program computes them — so nothing makes them
random variables of their own.

`record N, S` is the annotation that does. Written on a line of the program, it turns `N` and `S`
into coordinates of the trace from that point on. It denotes the one-point distribution at each, so
the program still computes the same measure (`thompsonRecord_eq`); all it does is put a `←` in the
program text where there was none, and a `←` is what the trace is built from.
-/

section Record

/-- The trace space of the annotated program: what the folding loop returned, then `N`, then `S`,
then `θ`. -/
abbrev RecordTrace (K : ℕ) : Type :=
  ((Fin K → ℝ) × (Fin K → ℝ)) × ((Fin K → ℝ) × ((Fin K → ℝ) × (Fin K → ℝ)))

/-- `thompson` again, with `N` and `S` recorded as random variables just before the sampling
loop. -/
def thompsonRecord (hK : 0 < K) (hist : Vector (Fin K × ℝ) n) : Measure (Fin K) := rdo
  let mut N : Fin K → ℝ := fun _ ↦ 1
  let mut S : Fin K → ℝ := fun _ ↦ 0
  for (a, r) in hist rdo
    N := fun j ↦ if j = a then N j + 1 else N j
    S := fun j ↦ if j = a then S j + r else S j
  record N, S
  let mut θ : Fin K → ℝ := fun _ ↦ 0
  for j in List.finRange K rdo
    let z ← gaussianReal (S j / N j) (Real.toNNReal (1 / N j))
    θ := fun k ↦ if k = j then z else θ k
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  return argmax θ

/-- **Recording is invisible to the semantics.** The annotated program is the same measure as
`thompson`; only its trace is finer. -/
theorem thompsonRecord_eq (hK : 0 < K) (hist : Vector (Fin K × ℝ) n) :
    thompsonRecord hK hist = thompson hK hist := by
  unfold thompsonRecord thompson
  simp (disch := is_markov) only [record_bind_of_isMarkov]

/-- The trace of the annotated program has four coordinates: what the folding loop returned, then
`N`, then `S`, then `θ`. `N` and `S` are deterministic given the fold — `rdo_peel` reports their
conditional law as a `Kernel.deterministic` — and the sampling loop's kernel is now a function of
*those* coordinates, which is what lets one condition on `N` and `S`. -/
example (hK : 0 < K) (hist : Vector (Fin K × ℝ) n) : True := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  rdo_trace (thompsonRecord (n := n) hK) with h
  rdo_peel h hist with hfold hN hS hθ hout
  -- `N` and `S`, now random variables, read off what the folding loop returned
  have _ : HasCondDistrib (fun ω : RecordTrace K ↦ ω.2.1) (fun ω ↦ ω.1) _ _ := hN
  have _ : HasCondDistrib (fun ω : RecordTrace K ↦ ω.2.2.1) (fun ω ↦ (ω.1, ω.2.1)) _ _ := hS
  -- `θ` drawn given them
  have _ : HasCondDistrib (fun ω : RecordTrace K ↦ ω.2.2.2)
      (fun ω ↦ ((ω.1, ω.2.1), ω.2.2.1)) _ _ := hθ
  -- and the action played is still Thompson sampling's
  rw [thompsonRecord_eq hK hist] at hout
  have _ : HasLaw (fun ω : RecordTrace K ↦ argmax ω.2.2.2) (thompson hK hist) _ := hout
  trivial

end Record

end RDo.Thompson

end

end
