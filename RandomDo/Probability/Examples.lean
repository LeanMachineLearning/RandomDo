/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import RandomDo.Probability.Tactic
public import RandomDo.Tactic.Elab

set_option linter.style.header false

/-!
# Reading probabilistic statements off an `rdo` program

Worked examples of `RDo.HasTrace`. Nothing here is specific to a particular distribution: the
programs draw from arbitrary Markov kernels, which is exactly what an `rdo` program does once
`is_markov` has run on its leaves.

The pattern is always the same.

1. Build the trace of the program bottom-up with the combinators of `RandomDo.Probability.Trace`,
   one per `rdo` construct. The trace kernel comes out as a right-nested `⊗ₖ`, one factor per `←`.
2. Fix the parameters `c`. The program's probability space is then `(Ω, P c)`, and the draws are
   the coordinates of `Ω`.
3. Peel the `⊗ₖ` factors off one at a time with `HasLaw.compProd_snd` / `Kernel.sectR_compProd` /
   `HasCondDistrib.compProd_fst` / `HasCondDistrib.compProd_snd`. Step `k` of the peeling hands
   you the conditional distribution of the `k`-th draw given the `k-1` draws before it.

Steps 1 and 3 are entirely mechanical, which is the point: `rdo_trace` and `rdo_peel` do them.
The `Automation` section at the end of this file re-derives, in two tactic calls, everything the
first two sections prove by hand.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RDo
open MeasurableSpacePure MeasurableSpaceBind

noncomputable section

/-! ## Two independent draws

```
rdo
  let x ← μ
  let y ← μ
  return x + y
```
-/

section Independent

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

/-- A program that draws twice from the same distribution. It takes no parameter, so its trace is
a kernel from `Unit`. -/
def sum2 : Measure ℝ := rdo
  let x ← μ
  let y ← μ
  return x + y

/-- The trace space of `sum2` is `ℝ × ℝ`, one coordinate per `←`, and the trace kernel is the
composition-product of the two draws. The second factor is a `Kernel.prodMkRight`, which records
in the *type* that the second draw does not look at the first. -/
lemma hasTrace_sum2 :
    HasTrace (fun _ : Unit ↦ sum2 μ)
      (Kernel.const Unit μ ⊗ₖ Kernel.prodMkRight ℝ (Kernel.const Unit μ))
      (fun p : Unit × (ℝ × ℝ) ↦ p.2.1 + p.2.2) := by
  have hfirst : HasTrace (fun _ : Unit ↦ μ) (Kernel.const Unit μ) Prod.snd :=
    (HasTrace.sample (Kernel.const Unit μ)).congr fun _ ↦ rfl
  have htail : HasTrace (fun p : Unit × ℝ ↦ μ >>=ₘ fun y ↦ mPure (p.2 + y))
      (Kernel.prodMkRight ℝ (Kernel.const Unit μ))
      (fun q : (Unit × ℝ) × ℝ ↦ q.1.2 + q.2) :=
    (hfirst.prodMkRight ℝ).bindPure (f := fun q : (Unit × ℝ) × ℝ ↦ q.1.2 + q.2) (by fun_prop)
  have hcont : Measurable fun p : Unit × ℝ ↦ μ >>=ₘ fun y ↦ mPure (p.2 + y) := by
    have : IsMarkov fun p : Unit × ℝ ↦ μ >>=ₘ fun y ↦ mPure (p.2 + y) := by is_markov
    exact this.measurable
  exact (hfirst.bind hcont htail).congr fun _ ↦ rfl

/-- The joint law of the two draws. -/
local notation "P₂" => (Kernel.const Unit μ ⊗ₖ Kernel.prodMkRight ℝ (Kernel.const Unit μ)) ()

/-- The first draw has law `μ`. -/
example : HasLaw (Prod.fst : ℝ × ℝ → ℝ) μ P₂ :=
  hasLaw_fst_compProd (Kernel.const Unit μ) (Kernel.prodMkRight ℝ (Kernel.const Unit μ)) ()

/-- The second draw has law `μ` too. -/
example : HasLaw (Prod.snd : ℝ × ℝ → ℝ) μ P₂ :=
  hasLaw_snd_compProd_prodMkRight (P := Kernel.const Unit μ) (R := Kernel.const Unit μ) ()

/-- And the two are independent: this is read off the `Kernel.prodMkRight` in the trace kernel,
which is itself read off the fact that the second `←` does not mention `x`. -/
example : IndepFun (Prod.fst : ℝ × ℝ → ℝ) Prod.snd P₂ :=
  indepFun_snd_compProd_prodMkRight (Kernel.const Unit μ) ()

/-- The program returns the sum of the two draws. Together with the three statements above, this
says exactly: `sum2 μ` is the law of `X + Y` for `X`, `Y` independent with law `μ`. -/
example : HasLaw (fun ω : ℝ × ℝ ↦ ω.1 + ω.2) (sum2 μ) P₂ := (hasTrace_sum2 μ).hasLaw_out ()

end Independent

/-! ## A dependent chain

```
rdo
  let x ← κ c
  let y ← η (c, x)
  let z ← θ ((c, x), y)
  return x + y + z
```

Every draw may read the parameter and all the draws before it. This is the general shape of a
straight-line `rdo` program: `κ`, `η`, `θ` stand for whatever `is_markov` produced at each `←`.
-/

section Chain

variable (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (η : Kernel (ℝ × ℝ) ℝ) [IsMarkovKernel η]
  (θ : Kernel ((ℝ × ℝ) × ℝ) ℝ) [IsMarkovKernel θ]

/-- Three draws, each depending on everything before it. -/
def chain (c : ℝ) : Measure ℝ := rdo
  let x ← κ c
  let y ← η (c, x)
  let z ← θ ((c, x), y)
  return x + y + z

lemma hasTrace_chain :
    HasTrace (chain κ η θ) (κ ⊗ₖ (η ⊗ₖ θ))
      (fun p : ℝ × (ℝ × (ℝ × ℝ)) ↦ p.2.1 + p.2.2.1 + p.2.2.2) := by
  have h3 : HasTrace (fun q : (ℝ × ℝ) × ℝ ↦ θ q >>=ₘ fun z ↦ mPure (q.1.2 + q.2 + z)) θ
      (fun r : ((ℝ × ℝ) × ℝ) × ℝ ↦ r.1.1.2 + r.1.2 + r.2) :=
    (HasTrace.sample θ).bindPure (f := fun r : ((ℝ × ℝ) × ℝ) × ℝ ↦ r.1.1.2 + r.1.2 + r.2)
      (by fun_prop)
  have hcont2 : Measurable fun q : (ℝ × ℝ) × ℝ ↦ θ q >>=ₘ fun z ↦ mPure (q.1.2 + q.2 + z) := by
    have : IsMarkov fun q : (ℝ × ℝ) × ℝ ↦ θ q >>=ₘ fun z ↦ mPure (q.1.2 + q.2 + z) := by
      is_markov
    exact this.measurable
  have h2 := (HasTrace.sample η).bind hcont2 h3
  have hcont1 : Measurable fun p : ℝ × ℝ ↦
      η p >>=ₘ fun y ↦ θ (p, y) >>=ₘ fun z ↦ mPure (p.2 + y + z) := by
    have : IsMarkov fun p : ℝ × ℝ ↦
        η p >>=ₘ fun y ↦ θ (p, y) >>=ₘ fun z ↦ mPure (p.2 + y + z) := by is_markov
    exact this.measurable
  exact ((HasTrace.sample κ).bind hcont1 h2).congr fun _ ↦ rfl

variable (c : ℝ)

/-- The joint law of the three draws, given the parameter `c`. -/
local notation "P₃" => (κ ⊗ₖ (η ⊗ₖ θ)) c

/-- **The mechanical peeling.** One `compProd_*` step per `←` in the program: `X` has law `κ c`,
`Y` given `X` has law `η (c, X)`, and `Z` given `(X, Y)` has law `θ ((c, X), Y)`. The kernels on
the right-hand sides are literally the ones written in the program. -/
example :
    HasLaw (fun ω : ℝ × (ℝ × ℝ) ↦ ω.1) (κ c) P₃
      ∧ HasCondDistrib (fun ω : ℝ × (ℝ × ℝ) ↦ ω.2.1) (fun ω ↦ ω.1) (Kernel.sectR η c) P₃
      ∧ HasCondDistrib (fun ω : ℝ × (ℝ × ℝ) ↦ ω.2.2) (fun ω ↦ (ω.1, ω.2.1))
          (θ.comap (fun p : ℝ × ℝ ↦ ((c, p.1), p.2)) (by fun_prop)) P₃ := by
  have h0 := hasLaw_id_compProd κ (η ⊗ₖ θ) c
  have htail := h0.compProd_snd
  rw [Kernel.sectR_compProd] at htail
  exact ⟨h0.compProd_fst, htail.compProd_fst, htail.compProd_snd⟩

/-- Unfolding what those kernels are: `Kernel.sectR η c x = η (c, x)`, so the middle statement
above really is "given `X = x`, the second draw is distributed as `η (c, x)`". -/
example (x : ℝ) : Kernel.sectR η c x = η (c, x) := Kernel.sectR_apply η x c

/-- The program's result, as a random variable on the trace space. -/
example : HasLaw (fun ω : ℝ × (ℝ × ℝ) ↦ ω.1 + ω.2.1 + ω.2.2) (chain κ η θ c) P₃ :=
  (hasTrace_chain κ η θ).hasLaw_out c

end Chain

/-! ## A loop, at coarse granularity

A `for` loop is a Markov kernel, so `HasTrace.of_isMarkov` (here in its `HasTrace.sample` form)
makes the whole loop *one* trace coordinate holding its result. That is enough to state the
conditional law of everything that comes after the loop given what the loop produced; it does not
decompose the loop's own iterations, which needs the extra machinery described in
`notes/TRACE_SEMANTICS.md`.
-/

section Loop

variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (η : Kernel ℝ ℝ) [IsMarkovKernel η]

/-- A loop summing `l.length` independent draws. -/
def loopPart (l : List ℕ) : Measure ℝ := rdo
  let mut S := 0
  for _ in l rdo
    let x ← μ
    S := S + x
  return S

instance (l : List ℕ) : IsProbabilityMeasure (loopPart μ l) := by
  unfold loopPart
  is_markov

/-- The loop, then a draw whose distribution depends on what the loop returned. -/
def loopThen (l : List ℕ) : Measure ℝ := rdo
  let S ← loopPart μ l
  let y ← η S
  return y

/-- The second `←` reads only the value the loop returned, i.e. the trace so far. -/
def afterLoopK : Kernel (Unit × ℝ) ℝ := η.comap Prod.snd measurable_snd

instance : IsMarkovKernel (afterLoopK η) := by
  unfold afterLoopK
  infer_instance

variable (l : List ℕ)

lemma hasTrace_loopThen :
    HasTrace (fun _ : Unit ↦ loopThen μ η l)
      (Kernel.const Unit (loopPart μ l) ⊗ₖ afterLoopK η)
      (fun p : Unit × (ℝ × ℝ) ↦ p.2.2) := by
  have hloop : HasTrace (fun _ : Unit ↦ loopPart μ l)
      (Kernel.const Unit (loopPart μ l)) Prod.snd :=
    (HasTrace.sample (Kernel.const Unit (loopPart μ l))).congr fun _ ↦ rfl
  have htail : HasTrace (fun p : Unit × ℝ ↦ η p.2) (afterLoopK η)
      (Prod.snd : (Unit × ℝ) × ℝ → ℝ) :=
    (HasTrace.sample (afterLoopK η)).congr fun _ ↦ rfl
  have hcont : Measurable fun p : Unit × ℝ ↦ η p.2 :=
    (Kernel.measurable η).comp measurable_snd
  exact (hloop.bind hcont htail).congr fun _ ↦ by unfold loopThen; rfl

/-- The loop's result has the loop's law. -/
example : HasLaw (Prod.fst : ℝ × ℝ → ℝ) (loopPart μ l)
    ((Kernel.const Unit (loopPart μ l) ⊗ₖ afterLoopK η) ()) :=
  hasLaw_fst_compProd (Kernel.const Unit (loopPart μ l)) (afterLoopK η) ()

/-- And given it, the draw that follows the loop has law `η S`. -/
example : HasCondDistrib (Prod.snd : ℝ × ℝ → ℝ) Prod.fst (Kernel.sectR (afterLoopK η) ())
    ((Kernel.const Unit (loopPart μ l) ⊗ₖ afterLoopK η) ()) :=
  hasCondDistrib_snd_compProd _ _ ()

example (S : ℝ) : Kernel.sectR (afterLoopK η) () S = η S := rfl

end Loop

/-! ## The same, automatically

`rdo_trace` walks the program and builds the trace; `rdo_peel` reads the laws off it. The
hypotheses they leave are exactly the statements proved by hand above.
-/

section Automation

variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
  (η : Kernel (ℝ × ℝ) ℝ) [IsMarkovKernel η] (θ : Kernel ((ℝ × ℝ) × ℝ) ℝ) [IsMarkovKernel θ]

/-- Two independent draws: the tactics find the trace, both laws, the independence, and the law of
the result. -/
example : True := by
  rdo_trace (sum2 μ) with h
  rdo_peel h () with hX hY hY' hindep hout
  -- `h : HasTrace (fun _ ↦ sum2 μ)
  --        (Kernel.const Unit μ ⊗ₖ Kernel.prodMkRight ℝ (Kernel.const Unit μ))
  --        (fun p ↦ p.2.1 + p.2.2)`
  have _ : HasLaw (Prod.fst : ℝ × ℝ → ℝ) μ _ := hX
  have _ : HasCondDistrib (Prod.snd : ℝ × ℝ → ℝ) Prod.fst _ _ := hY
  have _ : HasLaw (Prod.snd : ℝ × ℝ → ℝ) μ _ := hY'
  have _ : IndepFun (Prod.fst : ℝ × ℝ → ℝ) Prod.snd _ := hindep
  have _ : HasLaw (fun ω : ℝ × ℝ ↦ ω.1 + ω.2) (sum2 μ) _ := hout
  trivial

/-- The dependent chain: one conditional law per `←`, with the kernel written at that `←`. -/
example (c : ℝ) : True := by
  rdo_trace (chain κ η θ) with h
  rdo_peel h c with hX hY hZ hout
  have _ : HasLaw (fun ω : ℝ × (ℝ × ℝ) ↦ ω.1) (κ c) _ := hX
  have _ : HasCondDistrib (fun ω : ℝ × (ℝ × ℝ) ↦ ω.2.1) (fun ω ↦ ω.1)
      (η.comap (fun ω ↦ (c, ω)) (by fun_prop)) _ := hY
  have _ : HasCondDistrib (fun ω : ℝ × (ℝ × ℝ) ↦ ω.2.2) (fun ω ↦ (ω.1, ω.2.1))
      (θ.comap (fun p : ℝ × ℝ ↦ ((c, p.1), p.2)) (by fun_prop)) _ := hZ
  have _ : HasLaw (fun ω : ℝ × (ℝ × ℝ) ↦ ω.1 + ω.2.1 + ω.2.2) (chain κ η θ c) _ := hout
  trivial

end Automation

end

end
