/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import RandomDo.Monad.Instances
public import RandomDo.Monad.ForInInstances
public import RandomDo.Measurable
public import RandomDo.Tactic.ForInStep
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Data.List.OfFn
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Markov property of `rdo` programs

This file contains lemmas about the Markov property of `rdo` programs, i.e. measurability and
probability measure conditions. The purpose of this file is to propagate the `IsMarkov` property
through the constructs of the `rdo` language, allowing the `is_markov` tactic to automatically
verify that a given `rdo` program is Markovian or to reduce the proof of the Markov property of a
complex program to the Markov property/measurability of its underlying mathematical components.

## Main results
* `mPure_comp`: `rdo`'s `return e`, for an expression `e` depending measurably on the parameter, is
  Markovian.
* `measurable_bind`: Binding a Markov kernel `κ` with a family `η` that is jointly measurable in the
  parameter and in the bound variable is measurable in the parameter.
* `mBind`: Binding a Markov kernel `κ` with a family `η` that is Markovian in the parameter and in
  the bound variable is Markovian in the parameter.
* `gaussianReal`: A Gaussian distribution whose mean and variance depend measurably on the parameter
  is Markovian in the parameter.
* `comp`: Composing a Markov kernel `κ` with a measurable function `g` is Markovian in the
  parameter.
* `ite`: A conditional `rdo` program that chooses between two Markov kernels `κ` and `η` based on a
  measurable predicate `p` is Markovian in the parameter.
* `dite`: A dependent conditional `rdo` program that chooses between two Markov kernels `κ` and `η`
  based on a measurable predicate `p` is Markovian in the parameter.
* `forInList`: A `for` loop over a list, whose initial state depends measurably on the parameter and
  whose body is Markovian in the parameter and in the state, is Markovian in the parameter.
* `forInArray`, `forInVector`: The same statement for a `for` loop over an array or a vector.
* `forInList_comp`, `forInArray_comp`, `forInVector_comp`: The same three, for a loop over a
  collection the program takes as an argument. The body is then asked to be Markovian jointly in the
  parameter and in the element, which the fixed collections do not need.
* `breakRunK`: The case analysis a program performs after a loop that returns early, on the `Option`
  slot holding the returned value, is Markovian as soon as both of its branches are.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open MeasurableSpacePure

namespace IsMarkov

universe u v

variable {γ : Type*} [MeasurableSpace γ] {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
  {ι σ : Type v} [MeasurableSpace σ]

lemma mPure_comp {g : γ → α} (hg : Measurable g) : IsMarkov fun c ↦ (mPure (g c) : Measure α) := by
  refine ⟨Measure.measurable_dirac.comp hg, ?_⟩
  · intro c
    simp only [mPure_def]
    infer_instance

private lemma measurable_bind {κ : γ → Measure α} (hκ : IsMarkov κ)
    {η : γ → α → Measure β} (hη : Measurable (uncurry η)) :
    Measurable fun c ↦ (κ c).bind (η c) := by
  let κ' : Kernel γ α := hκ.toKernel
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  have hηc : ∀ c, Measurable (η c) := by
    intro c
    fun_prop
  simp_rw [Measure.bind_apply hs (hηc _).aemeasurable]
  exact Measurable.lintegral_kernel_prod_right (κ := κ') ((Measure.measurable_coe hs).comp hη)

lemma mBind {κ : γ → Measure α} (hκ : IsMarkov κ) {η : γ → α → Measure β}
    (hη : IsMarkov fun p : γ × α ↦ η p.1 p.2) : IsMarkov fun c ↦ κ c >>=ₘ η c := by
  have hη' : Measurable (uncurry η) := hη.measurable
  simp only [mBind_def]
  refine ⟨measurable_bind hκ hη', fun c ↦ ?_⟩
  · have := hκ.isProbabilityMeasure c
    refine isProbabilityMeasure_bind ?_ ?_
    · exact Measurable.aemeasurable (by fun_prop)
    · refine Filter.Eventually.of_forall fun a ↦ ?_
      exact hη.isProbabilityMeasure (c, a)

lemma gaussianReal {m : γ → ℝ} {v : γ → NNReal} (hm : Measurable m) (hv : Measurable v) :
    IsMarkov fun c ↦ ProbabilityTheory.gaussianReal (m c) (v c) :=
  ⟨ProbabilityTheory.measurable_gaussianReal.comp (hm.prodMk hv), fun _ ↦ inferInstance⟩

lemma comp {κ : γ → Measure α} (hκ : IsMarkov κ) {g : σ → γ} (hg : Measurable g) :
    IsMarkov fun c ↦ κ (g c) := ⟨hκ.measurable.comp hg, fun _ ↦ hκ.isProbabilityMeasure _⟩

lemma ite {p : γ → Prop} [DecidablePred p] (hp : Measurable p)
    {κ η : γ → Measure α} (hκ : IsMarkov κ) (hη : IsMarkov η) :
    IsMarkov fun c ↦ if p c then κ c else η c := by
  refine ⟨hκ.measurable.ite hp.setOf hη.measurable, fun c ↦ ?_⟩
  by_cases h : p c
  · simpa [h] using hκ.isProbabilityMeasure c
  · simpa [h] using hη.isProbabilityMeasure c

lemma dite {p : γ → Prop} [inst : DecidablePred p] (hp : Measurable p)
    {κ : {c // p c} → Measure α} (hκ : IsMarkov κ)
    {η : {c // ¬ p c} → Measure α} (hη : IsMarkov η) :
    IsMarkov fun c ↦ if h : p c then κ ⟨c, h⟩ else η ⟨c, h⟩ := by
  refine ⟨.dite (s := {c | p c}) hκ.measurable hη.measurable hp.setOf, fun c ↦ ?_⟩
  by_cases h : p c
  · simpa [h] using hκ.isProbabilityMeasure _
  · simpa [h] using hη.isProbabilityMeasure _

/-- The second half of one iteration of a `for` loop, shared by the two loops below: on `done b`
the loop stops there and hands back `b`, on `yield b` it carries on with `rest`. The continuation
`η` is left arbitrary and only asked to agree with that case analysis, so that each loop can pass
the `match` its own equation lemma produced. -/
private lemma loop_tail {η : (γ × σ) × ForInStep σ → Measure σ} {rest : γ → σ → Measure σ}
    (hrest : IsMarkov fun p : γ × σ ↦ rest p.1 p.2)
    (hdone : ∀ (p : γ × σ) (b : σ), η (p, .done b) = mPure b)
    (hyield : ∀ (p : γ × σ) (b : σ), η (p, .yield b) = rest p.1 b) :
    IsMarkov η := by
  refine IsMarkov.congr (hη := IsMarkov.forInStepCasesOn
      (done := fun (_ : γ × σ) (b : σ) ↦ (mPure b : Measure σ))
      (yield := fun (p : γ × σ) (b : σ) ↦ rest p.1 b)
      (IsMarkov.mPure_comp measurable_snd)
      (hrest.comp (g := fun r : (γ × σ) × σ ↦ (r.1.1, r.2)) (by fun_prop))) ?_
  rintro ⟨p, s⟩
  cases s with
  | done b => exact hdone p b
  | yield b => exact hyield p b

private lemma list_loop {as : List ι}
    {f : γ → (a : ι) → a ∈ as → σ → Measure (ForInStep σ)}
    (hf : ∀ a h, IsMarkov fun p : γ × σ ↦ f p.1 a h p.2) :
    ∀ as' (h : ∃ bs, bs ++ as' = as),
      IsMarkov fun p : γ × σ ↦ List.measurableSpaceForIn'.loop as (f p.1) as' p.2 h := by
  intro as'
  induction as' with
  | nil =>
    intro h
    simpa only [List.measurableSpaceForIn'.loop.eq_1] using
      IsMarkov.mPure_comp (g := fun p : γ × σ ↦ p.2) measurable_snd
  | cons a as' ih =>
    intro h
    obtain ⟨bs, rfl⟩ := h
    have h' : ∃ bs', bs' ++ as' = bs ++ a :: as' := ⟨bs ++ [a], by simp⟩
    simp only [List.measurableSpaceForIn'.loop.eq_2]
    refine IsMarkov.mBind ?_ ?_
    · infer_instance
    · refine loop_tail
        (rest := fun c b ↦ List.measurableSpaceForIn'.loop (bs ++ a :: as') (f c) as' b h') ?_ ?_ ?_
      · infer_instance
      · simp
      · simp

lemma forInList {as : List ι} {b : γ → σ} {f : γ → ι → σ → Measure (ForInStep σ)}
    (hb : Measurable b) (hf : ∀ a ∈ as, IsMarkov fun p : γ × σ ↦ f p.1 a p.2) :
    IsMarkov fun c ↦ MeasurableSpaceForIn.forIn (m := Measure) as (b c) (f c) :=
  (list_loop (f := fun c a _ s ↦ f c a s) hf as ⟨[], rfl⟩).comp
    (g := fun c ↦ (c, b c)) (measurable_id.prodMk hb)

private lemma array_loop {as : Array ι}
    {f : γ → (a : ι) → a ∈ as → σ → Measure (ForInStep σ)}
    (hf : ∀ a h, IsMarkov fun p : γ × σ ↦ f p.1 a h p.2) :
    ∀ i (h : i ≤ as.size),
      IsMarkov fun p : γ × σ ↦ Array.measurableSpaceForIn'.loop as (f p.1) i h p.2 := by
  intro i
  induction i with
  | zero =>
    intro h
    simpa only [Array.measurableSpaceForIn'.loop.eq_1] using
      IsMarkov.mPure_comp (g := fun p : γ × σ ↦ p.2) measurable_snd
  | succ i ih =>
    intro h
    have h' : i ≤ as.size := Nat.le_of_succ_le h
    simp only [Array.measurableSpaceForIn'.loop.eq_2]
    refine IsMarkov.mBind ?_ ?_
    · infer_instance
    · refine loop_tail
        (rest := fun c b ↦ Array.measurableSpaceForIn'.loop as (f c) i h' b) ?_ ?_ ?_
      · infer_instance
      · simp
      · simp

lemma forInArray {as : Array ι} {b : γ → σ} {f : γ → ι → σ → Measure (ForInStep σ)}
    (hb : Measurable b) (hf : ∀ a ∈ as, IsMarkov fun p : γ × σ ↦ f p.1 a p.2) :
    IsMarkov fun c ↦ MeasurableSpaceForIn.forIn (m := Measure) as (b c) (f c) :=
  (array_loop (f := fun c a _ s ↦ f c a s) hf as.size (Nat.le_refl _)).comp
    (g := fun c ↦ (c, b c)) (measurable_id.prodMk hb)

lemma forInVector {n : ℕ} {as : Vector ι n} {b : γ → σ} {f : γ → ι → σ → Measure (ForInStep σ)}
    (hb : Measurable b) (hf : ∀ a ∈ as, IsMarkov fun p : γ × σ ↦ f p.1 a p.2) :
    IsMarkov fun c ↦ MeasurableSpaceForIn.forIn (m := Measure) as (b c) (f c) :=
  forInArray hb fun a h ↦ hf a (by simpa using h)

section Unroll

/-- The denotation of a `for` loop over a list, as a plain structural recursion. -/
private noncomputable def listLoop (g : ι → σ → Measure (ForInStep σ)) :
    List ι → σ → Measure σ
  | [], b => mPure b
  | a :: l, b => g a b >>=ₘ fun step ↦
      ForInStep.casesOn (motive := fun _ => Measure σ) step mPure fun b' ↦ listLoop g l b'

/-- The reference implementation does not depend on the ambient list, only on the suffix being
traversed, as long as the body ignores the membership proofs. -/
private lemma loop_eq_listLoop (g : ι → σ → Measure (ForInStep σ)) :
    ∀ (l : List ι) (b : σ) (as : List ι) (f : (a : ι) → a ∈ as → σ → Measure (ForInStep σ))
      (_hf : ∀ a h b, f a h b = g a b) (h : ∃ bs, bs ++ l = as),
      List.measurableSpaceForIn'.loop as f l b h = listLoop g l b := by
  intro l
  induction l with
  | nil =>
    intro b as f _hf h
    rw [List.measurableSpaceForIn'.loop.eq_1]
    rfl
  | cons a l ih =>
    intro b as f hf h
    rw [List.measurableSpaceForIn'.loop.eq_2, hf]
    change _ = g a b >>=ₘ _
    refine MeasurableSpaceBind.bind_congr fun step ↦ ?_
    cases step with
    | done b' => rfl
    | yield b' => exact ih b' as f hf _

private lemma forIn_eq_listLoop (l : List ι) (b : σ) (g : ι → σ → Measure (ForInStep σ)) :
    MeasurableSpaceForIn.forIn (m := Measure) l b g = listLoop g l b :=
  loop_eq_listLoop g l b l _ (fun _ _ _ ↦ rfl) ⟨[], rfl⟩

private lemma forIn_nil (b : σ) (g : ι → σ → Measure (ForInStep σ)) :
    MeasurableSpaceForIn.forIn (m := Measure) ([] : List ι) b g = mPure b :=
  forIn_eq_listLoop _ _ _

private lemma forIn_cons (a : ι) (l : List ι) (b : σ) (g : ι → σ → Measure (ForInStep σ)) :
    MeasurableSpaceForIn.forIn (m := Measure) (a :: l) b g
      = g a b >>=ₘ fun step ↦ ForInStep.casesOn (motive := fun _ ↦ Measure σ) step mPure
          fun b' ↦ MeasurableSpaceForIn.forIn (m := Measure) l b' g := by
  rw [forIn_eq_listLoop]
  refine MeasurableSpaceBind.bind_congr fun step ↦ ?_
  cases step with
  | done b' => rfl
  | yield b' => exact (forIn_eq_listLoop l b' g).symm

/-- The array loop counts an index down from `as.size`, so at step `i` it is traversing the last
`i` elements of the underlying list. -/
private lemma arrayLoop_eq_listLoop (g : ι → σ → Measure (ForInStep σ)) (as : Array ι)
    (f : (a : ι) → a ∈ as → σ → Measure (ForInStep σ)) (hf : ∀ a h b, f a h b = g a b) :
    ∀ (i : ℕ) (h : i ≤ as.size) (b : σ),
      Array.measurableSpaceForIn'.loop as f i h b
        = listLoop g (as.toList.drop (as.size - i)) b := by
  intro i
  induction i with
  | zero =>
    intro h b
    have hnil : List.drop (as.size - 0) as.toList = [] := by simp
    rw [Array.measurableSpaceForIn'.loop.eq_1, hnil]
    rfl
  | succ i ih =>
    intro h b
    have hi : i < as.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) h
    have hk : as.size - (i + 1) < as.toList.length := by
      simp only [Array.length_toList]; omega
    rw [Array.measurableSpaceForIn'.loop.eq_2, hf, List.drop_eq_getElem_cons hk]
    have hidx : as.toList[as.size - (i + 1)] = as[as.size - 1 - i] := by
      rw [Array.getElem_toList]; congr 1; omega
    have hnext : as.size - (i + 1) + 1 = as.size - i := by omega
    rw [hidx, hnext]
    change _ = g as[as.size - 1 - i] b >>=ₘ _
    refine MeasurableSpaceBind.bind_congr fun step ↦ ?_
    cases step with
    | done b' => rfl
    | yield b' => exact ih (Nat.le_of_succ_le h) b'

/-- A `for` loop over an array is the loop over its underlying list. -/
private lemma forIn_array (as : Array ι) (b : σ) (g : ι → σ → Measure (ForInStep σ)) :
    MeasurableSpaceForIn.forIn (m := Measure) as b g
      = MeasurableSpaceForIn.forIn (m := Measure) as.toList b g := by
  rw [forIn_eq_listLoop]
  change Array.measurableSpaceForIn'.loop as _ as.size _ b = _
  rw [arrayLoop_eq_listLoop g as _ (fun _ _ _ ↦ rfl)]
  simp

end Unroll

section VaryingCollection

open Set

variable [MeasurableSpace ι]

/-- A family of measures indexed by a list is Markov as soon as it is Markov on every stratum. -/
private lemma of_prodList {δ : Type*} [MeasurableSpace δ] {κ : δ × List ι → Measure σ}
    (h : ∀ n, IsMarkov fun q : δ × (Fin n → ι) ↦ κ (q.1, List.ofFn q.2)) : IsMarkov κ := by
  refine ⟨measurable_of_prodList fun n ↦ (h n).measurable, ?_⟩
  rintro ⟨d, l⟩
  simpa only [List.ofFn_get] using (h l.length).isProbabilityMeasure (d, l.get)

/-- `forInList` for a list read off the parameter, as in a program taking the list it iterates over
as an argument. The element handed to the body then varies with the parameter, so the body has to be
Markovian jointly in the two — which the fixed case does not need, and which is why the elements are
asked for a measurable structure here only. -/
lemma forInList_comp {as : γ → List ι} {b : γ → σ}
    {f : γ → ι → σ → Measure (ForInStep σ)}
    (has : Measurable as) (hb : Measurable b)
    (hf : IsMarkov fun p : (γ × ι) × σ ↦ f p.1.1 p.1.2 p.2) :
    IsMarkov fun c ↦ MeasurableSpaceForIn.forIn (m := Measure) (as c) (b c) (f c) := by
  refine IsMarkov.comp ?_
    (κ := fun q : (γ × σ) × List ι ↦
      MeasurableSpaceForIn.forIn (m := Measure) q.2 q.1.2 (f q.1.1))
    (g := fun c ↦ ((c, b c), as c)) (by fun_prop)
  refine of_prodList fun n ↦ ?_
  induction n with
  | zero =>
    simp only [List.ofFn_zero, forIn_nil]
    exact mPure_comp (by fun_prop)
  | succ n ih =>
    simp only [List.ofFn_succ, forIn_cons]
    refine mBind (hf.comp (g := fun q : (γ × σ) × (Fin (n + 1) → ι) ↦ ((q.1.1, q.2 0), q.1.2))
      (by fun_prop)) ?_
    exact forInStepCasesOn
      (done := fun (_ : (γ × σ) × (Fin (n + 1) → ι)) (b' : σ) ↦ (mPure b' : Measure σ))
      (yield := fun (q : (γ × σ) × (Fin (n + 1) → ι)) (b' : σ) ↦
        MeasurableSpaceForIn.forIn (m := Measure) (List.ofFn fun i ↦ q.2 i.succ) b' (f q.1.1))
      (mPure_comp measurable_snd)
      (ih.comp (g := fun r : ((γ × σ) × (Fin (n + 1) → ι)) × σ ↦
        ((r.1.1.1, r.2), fun i ↦ r.1.2 i.succ)) (by fun_prop))

end VaryingCollection

/-- `forInArray` for an array read off the parameter. -/
lemma forInArray_comp [MeasurableSpace ι] {as : γ → Array ι} {b : γ → σ}
    {f : γ → ι → σ → Measure (ForInStep σ)}
    (has : Measurable as) (hb : Measurable b)
    (hf : IsMarkov fun p : (γ × ι) × σ ↦ f p.1.1 p.1.2 p.2) :
    IsMarkov fun c ↦ MeasurableSpaceForIn.forIn (m := Measure) (as c) (b c) (f c) := by
  simp_rw [forIn_array]
  exact forInList_comp (measurable_toList.comp has) hb hf

/-- `forInVector` for a vector read off the parameter. -/
lemma forInVector_comp [MeasurableSpace ι] {n : ℕ} {as : γ → Vector ι n} {b : γ → σ}
    {f : γ → ι → σ → Measure (ForInStep σ)}
    (has : Measurable as) (hb : Measurable b)
    (hf : IsMarkov fun p : (γ × ι) × σ ↦ f p.1.1 p.1.2 p.2) :
    IsMarkov fun c ↦ MeasurableSpaceForIn.forIn (m := Measure) (as c) (b c) (f c) :=
  forInArray_comp (by fun_prop) hb hf

private lemma measurable_breakRunK {o : α → Option γ} (ho : Measurable o)
    {breakK : α → β} {successK : α → γ → β} (h_break : Measurable breakK)
    (h_success : Measurable fun p : α × γ ↦ successK p.1 p.2) :
    Measurable fun a ↦ Break.runK (o a) (fun _ ↦ breakK a) (successK a) := by
  rcases isEmpty_or_nonempty γ with hγ | hne
  · have key : (fun a ↦ Break.runK (o a) (fun _ ↦ breakK a) (successK a)) = breakK := by
      funext a
      cases h : o a with
      | none => simp [Break.runK]
      | some r => exact hγ.elim r
    rw [key]
    exact h_break
  · obtain ⟨c₀⟩ := hne
    have key : (fun a ↦ Break.runK (o a) (fun _ ↦ breakK a) (successK a))
        = fun a ↦ if (o a).isSome then successK a ((o a).getD c₀) else breakK a := by
      funext a
      cases h : o a <;> simp [Break.runK]
    rw [key]
    refine Measurable.ite ?_ ?_ h_break
    · measurability
    · fun_prop

lemma breakRunK {o : α → Option γ} (ho : Measurable o)
    {breakK : α → Measure β} {successK : α → γ → Measure β} (h_break : IsMarkov breakK)
    (h_success : IsMarkov fun p : α × γ ↦ successK p.1 p.2) :
    IsMarkov fun a ↦ Break.runK (o a) (fun _ ↦ breakK a) (successK a) := by
  refine ⟨measurable_breakRunK ho h_break.measurable h_success.measurable, fun a ↦ ?_⟩
  cases h : o a with
  | none => simpa [Break.runK] using h_break.isProbabilityMeasure a
  | some r => simpa [Break.runK] using h_success.isProbabilityMeasure (a, r)

end IsMarkov
