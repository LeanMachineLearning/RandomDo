/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import RandomDo.ForMathlib.NumberTheory.FrobeniusNumber
public import RandomDo.ForMathlib.Probability.Kernel.Irreducible
public import RandomDo.ForMathlib.Probability.Kernel.SmallSet.Basic

/-!
# Aperiodic kernels

A kernel `κ : Kernel α α` is *periodic* with respect to a measure `π` if the space contains a
cycle of `d ≥ 2` disjoint measurable sets `D 0, ..., D (d - 1)`, the first of which has positive
`π`-measure, such that `κ` sends every point of `D i` to `D (i + 1)` almost surely. It is
*aperiodic* if it is not periodic.

## Main definitions

* `ProbabilityTheory.Kernel.IsAperiodic κ π`: the kernel `κ` has no cyclic decomposition of
  period at least 2 charged by `π`.

## Main statements

* `ProbabilityTheory.Kernel.IsAperiodic.exists_forall_pow_comp_apply_pos`: if `κ` is an
  irreducible aperiodic Markov kernel and `C` is a `(k, ν)`-small set, then `C` is reached from
  `ν` with positive probability in `n` steps for all `n` large enough.
* `ProbabilityTheory.Kernel.IsAperiodic.exists_forall_pow_apply_pos`: if `κ` is an irreducible
  aperiodic Markov kernel and `C` is a small set, then every point reaches `C` with positive
  probability in `n` steps for all `n` large enough.

## References

* [G. O. Roberts, J. S. Rosenthal, *General state space Markov chains and MCMC algorithms*,
  Probability Surveys, 2004][robertsrosenthal2004]
-/

@[expose] public section

open MeasureTheory Function

open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α α} {φ π ν : Measure α}

/-- A kernel `κ : Kernel α α` is aperiodic with respect to a measure `π` if there is no cycle of
`d ≥ 2` pairwise disjoint measurable sets `D 0, ..., D (d - 1)` with `π (D 0) > 0`, such that
`κ` sends every point of `D i` to `D (i + 1)` almost surely (indices are taken modulo `d`).
Ref. *Roberts-Rosenthal*, Section 3.2. -/
def IsAperiodic (κ : Kernel α α) (π : Measure α) : Prop :=
  ∀ (d : ℕ) (D : Fin (d + 2) → Set α), (∀ i, MeasurableSet (D i)) → Pairwise (Disjoint on D) →
    (∀ i, ∀ x ∈ D i, κ x (D (i + 1)) = 1) → π (D 0) = 0

/-- For an aperiodic kernel, all the sets of a cyclic decomposition have measure zero, not only
the first one. -/
lemma IsAperiodic.measure_eq_zero (hκ : κ.IsAperiodic π) {d : ℕ} {D : Fin (d + 2) → Set α}
    (hD : ∀ i, MeasurableSet (D i)) (hdisj : Pairwise (Disjoint on D))
    (h : ∀ i, ∀ x ∈ D i, κ x (D (i + 1)) = 1) (i : Fin (d + 2)) :
    π (D i) = 0 := by
  have h0 := hκ d (fun j ↦ D (i + j)) (fun j ↦ hD _)
    (hdisj.comp_of_injective (add_right_injective i))
    (fun j x hx ↦ by rw [← add_assoc]; exact h _ x hx)
  simpa using h0

/-- If a measurable set `S` is a null set for all the measures `(κ ^ m) ∘ₘ ν`, then it is
contained in a measurable `ν`-null set `B` whose complement is absorbing for `κ`: `κ y B = 0` for
all `y ∉ B`. -/
lemma exists_measurableSet_superset_forall_notMem_apply_eq_zero {S : Set α}
    (hS : MeasurableSet S) (h : ∀ m : ℕ, ((κ ^ m) ∘ₘ ν) S = 0) :
    ∃ B, MeasurableSet B ∧ S ⊆ B ∧ ν B = 0 ∧ ∀ y ∉ B, κ y B = 0 := by
  refine ⟨⋃ m : ℕ, {y | 0 < (κ ^ m) y S}, .iUnion fun m ↦ measurableSet_apply_pos _ hS,
    fun y hy ↦ Set.mem_iUnion.mpr ⟨0, ?_⟩, ?_, fun y hy ↦ ?_⟩
  · rw [Set.mem_ofPred_eq, pow_zero_apply, Measure.dirac_apply_of_mem hy]
    exact zero_lt_one
  · rw [measure_iUnion_null_iff]
    exact fun m ↦ (Measure.comp_apply_eq_zero_iff hS).mp (h m)
  · rw [measure_iUnion_null_iff]
    intro m
    rw [← Measure.comp_apply_eq_zero_iff hS, ← pow_succ_apply]
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt, nonpos_iff_eq_zero] at hy
    exact hy (m + 1)

open Fin.NatCast in
/-- Let `E : ℕ → Set α` be a family of measurable sets covering the space such that every point
which is sent to `E n` by `κ` with positive probability belongs to `E (n + 1)`. Let `B` be a
measurable set whose complement is absorbing for `κ` and which contains all the intersections
`E n₁ ∩ E n₂` for `n₁` and `n₂` not congruent modulo `d + 2`. If `κ` is aperiodic with respect to
`π`, then the complement of `B` is a `π`-null set.

Indeed, the sets `{y ∉ B | ∃ n, y ∈ E n ∧ d + 2 ∣ n + i}` for `i : Fin (d + 2)` form a cyclic
decomposition of the complement of `B`. -/
lemma IsAperiodic.measure_compl_eq_zero_of_inter_subset [IsMarkovKernel κ]
    (hκ : κ.IsAperiodic π) {d : ℕ} {E : ℕ → Set α} (hE : ∀ n, MeasurableSet (E n))
    (hcov : ∀ y, ∃ n, y ∈ E n) (hstep : ∀ y n, 0 < κ y (E n) → y ∈ E (n + 1))
    {B : Set α} (hB : MeasurableSet B) (hBabs : ∀ y ∉ B, κ y B = 0)
    (hEB : ∀ n₁ n₂, ¬ n₁ ≡ n₂ [MOD d + 2] → E n₁ ∩ E n₂ ⊆ B) :
    π Bᶜ = 0 := by
  have hcast {n₁ n₂ : ℕ} (h : (n₁ : Fin (d + 2)) ≠ n₂) : E n₁ ∩ E n₂ ⊆ B :=
    hEB n₁ n₂ fun h' ↦ h (Fin.ext (by simpa [Nat.ModEq] using h'))
  let D : Fin (d + 2) → Set α := fun i ↦ (⋃ n : ℕ, ⋃ (_ : (n : Fin (d + 2)) + i = 0), E n) \ B
  have hD_mem (i : Fin (d + 2)) (y : α) :
      y ∈ D i ↔ y ∉ B ∧ ∃ n : ℕ, (n : Fin (d + 2)) + i = 0 ∧ y ∈ E n := by
    simp [D, and_comm]
  have hD (i : Fin (d + 2)) : MeasurableSet (D i) :=
    (MeasurableSet.iUnion fun n ↦ .iUnion fun _ ↦ hE n).diff hB
  have hdisj : Pairwise (Disjoint on D) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro y hyi hyj
    obtain ⟨hyB, n, hn, hyn⟩ := (hD_mem i y).mp hyi
    obtain ⟨-, n', hn', hyn'⟩ := (hD_mem j y).mp hyj
    refine hyB (hcast (fun h ↦ hij ?_) ⟨hyn, hyn'⟩)
    rw [h] at hn
    exact add_left_cancel (hn.trans hn'.symm)
  have hD_step (i : Fin (d + 2)) (y : α) (hy : y ∈ D i) : κ y (D (i + 1)) = 1 := by
    obtain ⟨hyB, n₀, hn₀, hyn₀⟩ := (hD_mem i y).mp hy
    rw [← prob_compl_eq_zero_iff (hD _)]
    have hsub : (D (i + 1))ᶜ ⊆ B ∪ ⋃ n : ℕ, ⋃ (_ : (n : Fin (d + 2)) + (i + 1) ≠ 0), E n := by
      intro z hz
      by_cases hzB : z ∈ B
      · exact .inl hzB
      obtain ⟨n, hn⟩ := hcov z
      exact .inr (Set.mem_iUnion₂.mpr ⟨n, fun h ↦ hz ((hD_mem _ z).mpr ⟨hzB, n, h, hn⟩), hn⟩)
    refine measure_mono_null hsub (measure_union_null (hBabs y hyB) ?_)
    simp only [measure_iUnion_null_iff]
    intro n hn
    by_contra hpos
    refine hyB (hcast (fun h ↦ hn ?_) ⟨hstep y n (pos_iff_ne_zero.mpr hpos), hyn₀⟩)
    rw [← hn₀, ← h, Nat.cast_succ, add_assoc, add_comm 1 i]
  refine measure_mono_null (fun y hy ↦ ?_)
    (measure_iUnion_null (hκ.measure_eq_zero hD hdisj hD_step))
  obtain ⟨n, hn⟩ := hcov y
  exact Set.mem_iUnion.mpr ⟨-(n : Fin (d + 2)), (hD_mem _ y).mpr ⟨hy, n, add_neg_cancel _, hn⟩⟩

/-- Let `E : ℕ → Set α` be a family of measurable sets covering the space such that every point
which is sent to `E n` by `κ` with positive probability belongs to `E (n + 1)`. If `κ` is
aperiodic with respect to `π` and `ν ≪ π` is a nonzero measure then for every `d`, there are
`n₁` and `n₂` not congruent modulo `d + 2` such that `E n₁ ∩ E n₂` has positive measure for one of
the measures `(κ ^ m) ∘ₘ ν`. -/
lemma IsAperiodic.exists_pow_comp_inter_pos [IsMarkovKernel κ] (hκ : κ.IsAperiodic π)
    (hν : ν ≠ 0) (hνπ : ν ≪ π) {E : ℕ → Set α} (hE : ∀ n, MeasurableSet (E n))
    (hcov : ∀ y, ∃ n, y ∈ E n) (hstep : ∀ y n, 0 < κ y (E n) → y ∈ E (n + 1)) (d : ℕ) :
    ∃ m n₁ n₂ : ℕ, ¬ n₁ ≡ n₂ [MOD d + 2] ∧ 0 < ((κ ^ m) ∘ₘ ν) (E n₁ ∩ E n₂) := by
  by_contra! h
  simp only [nonpos_iff_eq_zero] at h
  obtain ⟨B, hB, hSB, hνB, hBabs⟩ := exists_measurableSet_superset_forall_notMem_apply_eq_zero
    (κ := κ) (ν := ν) (S := ⋃ n₁, ⋃ n₂, ⋃ (_ : ¬ n₁ ≡ n₂ [MOD d + 2]), E n₁ ∩ E n₂)
    (.iUnion fun n₁ ↦ .iUnion fun n₂ ↦ .iUnion fun _ ↦ (hE n₁).inter (hE n₂))
    (fun m ↦ by simpa only [measure_iUnion_null_iff] using h m)
  have hπB : π Bᶜ = 0 :=
    hκ.measure_compl_eq_zero_of_inter_subset (d := d) hE hcov hstep hB hBabs fun n₁ n₂ hn y hy ↦
      hSB (Set.mem_iUnion₂.mpr ⟨n₁, n₂, Set.mem_iUnion.mpr ⟨hn, hy⟩⟩)
  refine hν (Measure.measure_univ_eq_zero.mp ?_)
  rw [← Set.union_compl_self B]
  exact measure_union_null hνB (hνπ hπB)

/-- If `κ` is a `φ`-irreducible Markov kernel which is aperiodic with respect to `π`, and `C` is a
`(k, ν)`-small set with `ν ≪ π` and `φ C > 0`, then starting from `ν`, the set `C` is reached
with positive probability in `n` steps for all `n` large enough. -/
lemma IsAperiodic.exists_forall_pow_comp_apply_pos [IsMarkovKernel κ] [IsIrreducible φ κ]
    (hκ : κ.IsAperiodic π) {C : Set α} (hC : MeasurableSet C) (hφC : 0 < φ C) {k : ℕ}
    (hk : 0 < k) (hν : ν ≠ 0) (hνπ : ν ≪ π) (hsmall : IsSmallSet κ C k ν) :
    ∃ N : ℕ, ∀ n ≥ N, 0 < ((κ ^ n) ∘ₘ ν) C := by
  -- the set of times at which `C` is reached from `ν`, shifted by `k`, is closed under addition
  let T : Set ℕ := (· + k) '' {n : ℕ | 0 < ((κ ^ n) ∘ₘ ν) C}
  have hT_add : ∀ a ∈ T, ∀ b ∈ T, a + b ∈ T := by
    rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
    exact ⟨m + k + n, hsmall.pow_comp_apply_pos_of_pow_comp_apply_pos hC hn hm, by ring⟩
  -- it suffices to prove that its gcd is 1
  suffices hgcd : Nat.setGcd T = 1 by
    obtain ⟨N, hN⟩ := Nat.exists_forall_ge_mem_of_setGcd_eq_one hT_add hgcd
    refine ⟨N, fun n hn ↦ ?_⟩
    obtain ⟨m, hm, hmn⟩ := hN (n + k) (by omega)
    obtain rfl : m = n := by simpa using hmn
    exact hm
  by_contra hgcd
  obtain ⟨n₀, hn₀⟩ := IsIrreducible.exists_pow_comp_apply_pos (φ := φ) (κ := κ) hC hφC hν
  have h0 : Nat.setGcd T ≠ 0 := by
    rw [Ne, Nat.setGcd_eq_zero_iff]
    intro h
    have : n₀ + k = 0 := h ⟨n₀, hn₀, rfl⟩
    omega
  obtain ⟨d, hd⟩ : ∃ d, Nat.setGcd T = d + 2 := ⟨Nat.setGcd T - 2, by omega⟩
  have hdvd (n : ℕ) (hn : 0 < ((κ ^ n) ∘ₘ ν) C) : d + 2 ∣ n + k :=
    hd ▸ Nat.setGcd_dvd_of_mem ⟨n, hn, rfl⟩
  -- otherwise, we get two times with different phases reachable from the same points
  obtain ⟨m, n₁, n₂, hne, hpos⟩ := hκ.exists_pow_comp_inter_pos hν hνπ
    (E := fun n ↦ {y | 0 < (κ ^ n) y C}) (fun n ↦ measurableSet_apply_pos _ hC)
    (IsIrreducible.irreducible (φ := φ) hC hφC) (fun y n h ↦ (pow_succ_apply_pos_iff hC).mpr h) d
  have h₁ : d + 2 ∣ n₁ + m + k := hdvd _ ((pow_add_comp_apply_pos_iff hC).mpr
    (hpos.trans_le (measure_mono Set.inter_subset_left)))
  have h₂ : d + 2 ∣ n₂ + m + k := hdvd _ ((pow_add_comp_apply_pos_iff hC).mpr
    (hpos.trans_le (measure_mono Set.inter_subset_right)))
  have h₁₂ : n₁ + m + k ≡ n₂ + m + k [MOD d + 2] :=
    ((Nat.modEq_zero_iff_dvd).mpr h₁).trans ((Nat.modEq_zero_iff_dvd).mpr h₂).symm
  exact hne (Nat.ModEq.add_right_cancel' _ (Nat.ModEq.add_right_cancel' _ h₁₂))

/-- If `κ` is a `φ`-irreducible Markov kernel which is aperiodic with respect to `π`, and `C` is a
`(k, ν)`-small set with `ν ≪ π` and `φ C > 0`, then from every point `x`, the set `C` is reached
with positive probability in `n` steps for all `n` large enough.
Ref. *Roberts-Rosenthal*, proof of Theorem 4. -/
theorem IsAperiodic.exists_forall_pow_apply_pos [IsMarkovKernel κ] [IsIrreducible φ κ]
    (hκ : κ.IsAperiodic π) {C : Set α} (hC : MeasurableSet C) (hφC : 0 < φ C) {k : ℕ}
    (hk : 0 < k) (hν : ν ≠ 0) (hνπ : ν ≪ π) (hsmall : IsSmallSet κ C k ν) (x : α) :
    ∃ N, ∀ n ≥ N, 0 < (κ ^ n) x C := by
  obtain ⟨N, hN⟩ := hκ.exists_forall_pow_comp_apply_pos hC hφC hk hν hνπ hsmall
  obtain ⟨n₁, hn₁⟩ := IsIrreducible.irreducible (φ := φ) (κ := κ) hC hφC x
  refine ⟨N + k + n₁, fun n hn ↦ ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + k + n₁ := ⟨n - (k + n₁), by omega⟩
  exact hsmall.pow_apply_pos_of_pow_comp_apply_pos hn₁ (hN m (by omega))

end ProbabilityTheory.Kernel
