module

public import RandomDo.Monad.Notation
public import RandomDo.Monad.Instances
public import RandomDo.Monad.ForInInstances
public import RandomDo.Tactic.IsMarkov.ForInStep
public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace
public import Mathlib.Probability.Kernel.Representation
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.HasCondDistrib
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Bernoulli

set_option linter.style.header false

/-!
# Prototype: random variables for `rdo` programs from a table of uniform random numbers

## The idea

Fix one probability space for every program: a *table* `ω` holding one independent uniform
number in `[0,1]` at every *address*, an address being a finite list of natural numbers.

A program run against a table is deterministic. Each draw `let x ← κ c` reads one entry of the
table and turns it into a value with a measurable *sampler* for `κ` (Mathlib's
`Kernel.exists_measurable_map_eq_unitInterval`: every Markov kernel into a standard Borel space
is the image of the uniform measure on `[0,1]` by a jointly measurable map). So every value the
program computes, including every intermediate draw, is a random variable on the table.

Which entry a draw reads is decided by one rule: *each part of the program gets its own part of
the table*. In `let x ← p; q x`, `p` reads the entries whose address starts with `0`, and `q x`
those whose address starts with `1`; a single draw reads the entry at address `[]` of its part.
Loops unfold into nested binds and recursive calls are binds too, so they need no special
treatment, and two different draws never read the same entry.

Everything probabilistic then follows from one fact, `hasCondDistrib_fresh`: a draw reading a
part of the table that the random variable `C` never looks at has the right conditional law
given `C`. That is independence of disjoint sets of table entries.

## How programs are written

A program is written once, for any monad `m` with a `sample` operation (`HasSample`), as the
programs of `Polymorphic.lean` and `Bandits/Defs.lean` already are. At `m := Measure` it is the
usual `rdo` program, a measure. At `m := Src` it is a function of the table. `Realizes` links the
two: pushing the uniform table through the `Src` version gives the `Measure` version.

## Contents

* `§ The table`, `§ Independence`: the probability space and the independence of disjoint entries.
* `§ Programs reading the table`: the monad `Src`, `sample`, and `Realizes`.
* `§ Example 1`: `sumTwo`, two independent draws.
* `§ Example 2`: a chain of three draws, each depending on the previous ones.
* `§ Example 3`: a loop with a branch inside. A draw in a branch not taken is still a random
  variable, independent of everything before it.
* `§ Example 4`: an algorithm interacting with an environment, both given by programs, is an
  `IsAlgEnvSeq` (`Interaction.isAlgEnvSeq`). For ε-greedy, the internal coin and uniform arm
  are random variables on the same space, which gives the exploration bound directly
  (`Interaction.le_map_A`), and on any other space by uniqueness of the trajectory law
  (`Interaction.le_map_action`).

## What is not done here

* `realize` proves `Realizes` for `return`, `←`, `if`, `for` over a list, `sample` and `draw`;
  `match`, `dite`, early `break`/`return` in loops and loops over arrays are not covered yet.
* The random variables of a program (`X`, `Y`, `B k`, `Z k`, …) are written by hand, reading off
  the address of each draw. The addresses follow the *elaborated* program (see `Unif`), so a
  tactic reading them off would be the next step.
* In `Interaction`, the loop over rounds is written by hand, with round `n` reading the part of the
  table under `[n]`. Written as an `rdo` recursion over the horizon, the address of round `n`
  would depend on the horizon.
-/

open MeasureTheory ProbabilityTheory unitInterval Function
open scoped ENNReal
open MeasurableSpacePure MeasurableSpaceBind

@[expose] public section

noncomputable section

namespace RDo.RandomSource

/-! ## The table -/

/-- An address in the table. -/
abbrev Addr := List ℕ

/-- A table of numbers in `[0,1]`, one per address. -/
abbrev Table := Addr → I

/-- The law of the table: every entry uniform on `[0,1]`, all entries independent. -/
def U : Measure Table := Measure.infinitePi fun _ ↦ volume

instance : IsProbabilityMeasure U := by unfold U; infer_instance

/-- The part of the table under the address `pre`: the entries whose address starts with `pre`. -/
def subAt (pre : Addr) (ω : Table) : Table := fun a ↦ ω (pre ++ a)

@[fun_prop]
lemma measurable_subAt (pre : Addr) : Measurable (subAt pre) := by
  unfold subAt; fun_prop

/-- A part of the table is again a uniform table. -/
lemma map_subAt (pre : Addr) : U.map (subAt pre) = U := by
  unfold U subAt
  exact Measure.map_infinitePi_infinitePi_of_inj (List.append_right_injective pre)

lemma dependsOn_subAt (pre : Addr) : DependsOn (subAt pre) {a | pre <+: a} :=
  fun _ _ h ↦ funext fun a ↦ h _ (List.prefix_append pre a)

/-- A single entry of the table is uniform. -/
lemma map_eval (a : Addr) : U.map (fun ω ↦ ω a) = volume := by
  unfold U; exact Measure.infinitePi_map_eval _ a

/-! ## Independence

Random variables reading disjoint sets of entries are independent. "Reading only the entries in
`S`" is Mathlib's `DependsOn F S`.
-/

open Classical in
/-- Complete a partial table by zeros. -/
def fill (S : Set Addr) (v : S → I) : Table := fun a ↦ if h : a ∈ S then v ⟨a, h⟩ else 0

lemma measurable_fill (S : Set Addr) : Measurable (fill S) := by
  classical
  refine measurable_pi_iff.mpr fun a ↦ ?_
  by_cases h : a ∈ S
  · simpa [fill, h] using measurable_pi_apply (⟨a, h⟩ : S)
  · simp [fill, h]

lemma eq_fill_of_dependsOn {X : Type*} {F : Table → X} {S : Set Addr} (hF : DependsOn F S)
    (ω : Table) : F ω = F (fill S fun a ↦ ω a) :=
  hF fun a ha ↦ by simp [fill, ha]

/-- A measurable random variable reading only the entries in `S` is measurable for the σ-algebra
generated by those entries. -/
lemma comap_le_iSup {X : Type*} [MeasurableSpace X] {F : Table → X} (hF : Measurable F)
    {S : Set Addr} (hFS : DependsOn F S) :
    MeasurableSpace.comap F inferInstance
      ≤ ⨆ a ∈ S, MeasurableSpace.comap (fun ω : Table ↦ ω a) inferInstance := by
  set m := ⨆ a ∈ S, MeasurableSpace.comap (fun ω : Table ↦ ω a) inferInstance
  have hr : Measurable[m] (fun ω : Table ↦ fun a : S ↦ ω a) := by
    refine @Measurable.of_eval Table S (fun _ ↦ I) m _ _ fun a ↦ ?_
    exact (comap_measurable (fun ω : Table ↦ ω a)).mono (le_iSup₂_of_le (a : Addr) a.2 le_rfl)
      le_rfl
  have hG : Measurable[m] F := by
    rw [show F = (F ∘ fill S) ∘ (fun ω : Table ↦ fun a : S ↦ ω a) from
      funext (eq_fill_of_dependsOn hFS)]
    exact (hF.comp (measurable_fill S)).comp hr
  exact hG.comap_le

lemma iIndep_entries :
    iIndep (fun a ↦ MeasurableSpace.comap (fun ω : Table ↦ ω a) inferInstance) U :=
  (iIndepFun_iff_iIndep _ _ _).1
    (iIndepFun_infinitePi (P := fun _ : Addr ↦ (volume : Measure I)) (X := fun _ x ↦ x)
      fun _ ↦ measurable_id)

/-- **Independence.** Random variables reading disjoint sets of entries are independent. -/
theorem indepFun_of_dependsOn {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {F : Table → X} {G : Table → Y} (hF : Measurable F) (hG : Measurable G) {S T : Set Addr}
    (hFS : DependsOn F S) (hGT : DependsOn G T) (hST : Disjoint S T) : IndepFun F G U := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_right
    (indep_of_indep_of_le_left
      (indep_iSup_of_disjoint (fun a ↦ (measurable_pi_apply a).comap_le) iIndep_entries hST)
      (comap_le_iSup hF hFS))
    (comap_le_iSup hG hGT)

/-! ## Programs reading the table -/

/-- A program run against the table: a function of the table. -/
abbrev Src (α : Type) [MeasurableSpace α] : Type := Table → α

/-- The monad structure: `mBind p q` runs `p` on the part of the table under `[0]`, and the
continuation on the part under `[1]`. -/
instance : MeasurableSpaceMonad Src where
  mPure a := fun _ ↦ a
  mBind p q := fun ω ↦ q (p (subAt [0] ω)) (subAt [1] ω)

/-- Programs that can draw from a Markov kernel. -/
class HasSample (m : (α : Type) → [MeasurableSpace α] → Type) where
  /-- Draw from the kernel `κ` at the parameter `c`. -/
  sample {γ α : Type} [MeasurableSpace γ] [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (κ : Kernel γ α) [IsMarkovKernel κ] (c : γ) : m α

noncomputable instance : HasSample Measure where
  sample κ _ c := κ c

section Sample

variable {γ α : Type} [MeasurableSpace γ] [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

/-- A sampler for `κ`: a jointly measurable map turning a uniform number into a draw from `κ c`. -/
def sampler (κ : Kernel γ α) [IsMarkovKernel κ] : γ → I → α :=
  (κ.exists_measurable_map_eq_unitInterval).choose

@[fun_prop]
lemma measurable_sampler (κ : Kernel γ α) [IsMarkovKernel κ] : Measurable (uncurry (sampler κ)) :=
  (κ.exists_measurable_map_eq_unitInterval).choose_spec.1

@[fun_prop]
lemma measurable_sampler' (κ : Kernel γ α) [IsMarkovKernel κ] {δ : Type*} [MeasurableSpace δ]
    {f : δ → γ} {g : δ → I} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun d ↦ sampler κ (f d) (g d) :=
  (measurable_sampler κ).comp (hf.prodMk hg)

lemma map_sampler (κ : Kernel γ α) [IsMarkovKernel κ] (c : γ) :
    volume.map (sampler κ c) = κ c :=
  (κ.exists_measurable_map_eq_unitInterval).choose_spec.2 c

/-- A draw reads the entry at address `[]` of its part of the table. -/
instance : HasSample Src where
  sample κ _ c := fun ω ↦ sampler κ c (ω [])

/-- The draw from `κ c` that reads the entry at address `a`, as a random variable. -/
lemma hasLaw_sampler (κ : Kernel γ α) [IsMarkovKernel κ] (c : γ) (a : Addr) :
    HasLaw (fun ω : Table ↦ sampler κ c (ω a)) (κ c) U where
  aemeasurable := (measurable_sampler' κ measurable_const (measurable_pi_apply a)).aemeasurable
  map_eq := by
    have h : Measurable (sampler κ c) := (measurable_sampler κ).comp measurable_prodMk_left
    change U.map (sampler κ c ∘ fun ω ↦ ω a) = _
    rw [← Measure.map_map h (measurable_pi_apply a), map_eval, map_sampler]

end Sample

/-! ### `Realizes`: the table program computes the `Measure` program -/

section Realizes

variable {γ δ α β : Type} [MeasurableSpace γ] [MeasurableSpace δ] [MeasurableSpace α]
  [MeasurableSpace β]

/-- `Realizes p μ`: pushing the uniform table through the table program `p c` gives the measure
`μ c`, for every parameter `c`, and `p` is jointly measurable in the parameter and the table. -/
structure Realizes (p : γ → Src α) (μ : γ → Measure α) : Prop where
  measurable : Measurable fun x : γ × Table ↦ p x.1 x.2
  map_eq (c : γ) : U.map (p c) = μ c

/-- The law of a family of table programs, as a kernel. -/
def lawK (p : γ → Src α) : Kernel γ α :=
  (Kernel.id ×ₖ Kernel.const γ U).map fun x ↦ p x.1 x.2

lemma lawK_apply {p : γ → Src α} (hp : Measurable fun x : γ × Table ↦ p x.1 x.2) (c : γ) :
    lawK p c = U.map (p c) := by
  rw [lawK, Kernel.map_apply _ hp, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod, Measure.map_map hp measurable_prodMk_left]
  rfl

lemma isMarkovKernel_lawK {p : γ → Src α} (hp : Measurable fun x : γ × Table ↦ p x.1 x.2) :
    IsMarkovKernel (lawK p) := by
  unfold lawK; exact Kernel.IsMarkovKernel.map _ hp

/-- The law of a realized family is the kernel it realizes. -/
lemma Realizes.lawK_eq {p : γ → Src α} {κ : Kernel γ α} (h : Realizes p κ) : lawK p = κ :=
  Kernel.ext fun c ↦ by rw [lawK_apply h.measurable, h.map_eq]

/-- Drawing `x` from `μ` and, independently, `y` from `ν`, then computing `f x y`: the pair
`(x, f x y)` has law `μ ⊗ₘ κ` when `f x` pushes `ν` to `κ x`. -/
lemma map_prod_eq_compProd' {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} [SFinite μ] {ν : Measure Y} [SFinite ν] {f : X → Y → α}
    (hf : Measurable (uncurry f)) {κ : Kernel X α} [IsSFiniteKernel κ]
    (hκ : ∀ x, ν.map (f x) = κ x) :
    (μ.prod ν).map (fun p ↦ (p.1, f p.1 p.2)) = μ ⊗ₘ κ := by
  have hf' : Measurable fun p : X × Y ↦ (p.1, f p.1 p.2) := measurable_fst.prodMk hf
  ext s hs
  rw [Measure.map_apply hf' hs, Measure.prod_apply (hf' hs), Measure.compProd_apply hs]
  refine lintegral_congr fun x ↦ ?_
  have hfx : Measurable (f x) := hf.comp measurable_prodMk_left
  rw [← hκ, Measure.map_apply hfx (measurable_prodMk_left hs)]
  rfl

/-- Running `q` on a fresh table next to a random parameter drawn from `μ`: the parameter, and
the result of `q` on it, have joint law `μ ⊗ₘ lawK q`. -/
lemma map_prod_eq_compProd {μ : Measure γ} [SFinite μ] {q : γ → Src α}
    (hq : Measurable fun x : γ × Table ↦ q x.1 x.2) :
    (μ.prod U).map (fun x ↦ (x.1, q x.1 x.2)) = μ ⊗ₘ lawK q := by
  have := isMarkovKernel_lawK hq
  exact map_prod_eq_compProd' (f := q) hq fun x ↦ (lawK_apply hq x).symm

lemma Realizes.pure {g : γ → α} (hg : Measurable g) :
    Realizes (fun c ↦ (mPure (g c) : Src α)) (fun c ↦ (mPure (g c) : Measure α)) where
  measurable := hg.comp measurable_fst
  map_eq c := by
    change U.map (fun _ ↦ g c) = Measure.dirac (g c)
    rw [Measure.map_const, measure_univ, one_smul]

lemma Realizes.comp {p : γ → Src α} {μ : γ → Measure α} (h : Realizes p μ) {g : δ → γ}
    (hg : Measurable g) : Realizes (fun d ↦ p (g d)) (fun d ↦ μ (g d)) where
  measurable := h.measurable.comp ((hg.comp measurable_fst).prodMk measurable_snd)
  map_eq d := h.map_eq (g d)

lemma Realizes.sample [StandardBorelSpace α] [Nonempty α] (κ : Kernel γ α) [IsMarkovKernel κ] :
    Realizes (fun c ↦ (HasSample.sample κ c : Src α)) (fun c ↦ (HasSample.sample κ c : Measure α))
    where
  measurable := by
    change Measurable fun x : γ × Table ↦ sampler κ x.1 (x.2 [])
    fun_prop
  map_eq c := (hasLaw_sampler κ c []).map_eq

/-- The two halves of the table are independent uniform tables. -/
lemma map_split : U.map (fun ω ↦ (subAt [0] ω, subAt [1] ω)) = U.prod U := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).1
    (indepFun_of_dependsOn (by fun_prop) (by fun_prop) (dependsOn_subAt [0]) (dependsOn_subAt [1])
      ?_), map_subAt, map_subAt]
  refine Set.disjoint_left.mpr fun a h₀ h₁ ↦ ?_
  obtain ⟨_, rfl⟩ := h₀
  obtain ⟨_, h⟩ := h₁
  simp at h

/-- **Bind.** -/
lemma Realizes.bind {p : γ → Src α} {μ : γ → Measure α} {q : γ → α → Src β}
    {ν : γ → α → Measure β} (hp : Realizes p μ)
    (hq : Realizes (fun x : γ × α ↦ q x.1 x.2) (fun x ↦ ν x.1 x.2)) :
    Realizes (fun c ↦ p c >>=ₘ q c) (fun c ↦ μ c >>=ₘ ν c) where
  measurable := by
    change Measurable fun x : γ × Table ↦ q x.1 (p x.1 (subAt [0] x.2)) (subAt [1] x.2)
    have hp' := hp.measurable
    have hq' := hq.measurable
    have h₀ : Measurable fun x : γ × Table ↦ subAt [0] x.2 := by fun_prop
    have h₁ : Measurable fun x : γ × Table ↦ subAt [1] x.2 := by fun_prop
    exact hq'.comp ((measurable_fst.prodMk (hp'.comp (measurable_fst.prodMk h₀))).prodMk h₁)
  map_eq c := by
    have hpc : Measurable (p c) := hp.measurable.comp measurable_prodMk_left
    have hqc : Measurable fun x : α × Table ↦ q c x.1 x.2 :=
      hq.measurable.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    have hsplit : Measurable fun ω ↦ (subAt [0] ω, subAt [1] ω) := by fun_prop
    change U.map (fun ω ↦ q c (p c (subAt [0] ω)) (subAt [1] ω)) = (μ c).bind (ν c)
    have hν : ν c = fun a ↦ lawK (q c) a := funext fun a ↦ by
      rw [lawK_apply hqc]; exact (hq.map_eq (c, a)).symm
    have hprod : (U.map (p c)).prod U = (U.prod U).map (Prod.map (p c) id) := by
      rw [← Measure.map_prod_map _ _ hpc measurable_id, Measure.map_id]
    calc U.map (fun ω ↦ q c (p c (subAt [0] ω)) (subAt [1] ω))
      _ = (U.prod U).map (fun x ↦ q c (p c x.1) x.2) := by
        have h : Measurable fun x : Table × Table ↦ q c (p c x.1) x.2 :=
          hqc.comp ((hpc.comp measurable_fst).prodMk measurable_snd)
        rw [← map_split, Measure.map_map h hsplit]
        rfl
      _ = Measure.snd (((U.map (p c)).prod U).map (fun x ↦ (x.1, q c x.1 x.2))) := by
        have h1 : Measurable fun x : α × Table ↦ (x.1, q c x.1 x.2) := measurable_fst.prodMk hqc
        have h2 : Measurable (Prod.map (p c) (id : Table → Table)) := hpc.prodMap measurable_id
        rw [Measure.snd, hprod, Measure.map_map h1 h2, Measure.map_map measurable_snd (h1.comp h2)]
        rfl
      _ = (μ c).bind (ν c) := by
        have := isMarkovKernel_lawK hqc
        rw [map_prod_eq_compProd hqc, ← hp.map_eq c, Measure.snd_compProd, hν]

/-- **Branching.** -/
lemma Realizes.ite {P : γ → Prop} [DecidablePred P] (hP : MeasurableSet {c | P c})
    {p₁ p₂ : γ → Src α} {μ₁ μ₂ : γ → Measure α} (h₁ : Realizes p₁ μ₁) (h₂ : Realizes p₂ μ₂) :
    Realizes (fun c ↦ if P c then p₁ c else p₂ c) (fun c ↦ if P c then μ₁ c else μ₂ c) where
  measurable := by
    have : (fun x : γ × Table ↦ (if P x.1 then p₁ x.1 else p₂ x.1) x.2)
        = fun x ↦ if P x.1 then p₁ x.1 x.2 else p₂ x.1 x.2 := by
      ext x; split_ifs <;> rfl
    rw [this]
    exact Measurable.ite (measurable_fst hP) h₁.measurable h₂.measurable
  map_eq c := by
    by_cases hc : P c
    · simpa [hc] using h₁.map_eq c
    · simpa [hc] using h₂.map_eq c

end Realizes

/-! ### Fresh parts of the table -/

section Fresh

variable {X α : Type} [MeasurableSpace X] [MeasurableSpace α]

/-- **The key lemma.** Let `C` be a random variable that reads only the entries in `S`, and run
the program `q (C ω)` on the part of the table under `pre`, which `C` never reads. Then, given
`C`, the result has the law of the program `q` at `C`. -/
theorem hasCondDistrib_fresh {C : Table → X} (hC : Measurable C) {S : Set Addr}
    (hCS : DependsOn C S) {pre : Addr} (hpre : ∀ a ∈ S, ¬ pre <+: a) {q : X → Src α}
    (hq : Measurable fun x : X × Table ↦ q x.1 x.2) :
    HasCondDistrib (fun ω ↦ q (C ω) (subAt pre ω)) C (lawK q) U where
  aemeasurable := by
    exact (hC.prodMk (hq.comp (hC.prodMk (measurable_subAt pre)))).aemeasurable
  map_eq := by
    have hind : IndepFun C (subAt pre) U :=
      indepFun_of_dependsOn hC (measurable_subAt pre) hCS (dependsOn_subAt pre)
        (Set.disjoint_left.mpr fun a ha ha' ↦ hpre a ha ha')
    calc U.map (fun ω ↦ (C ω, q (C ω) (subAt pre ω)))
      _ = (U.map fun ω ↦ (C ω, subAt pre ω)).map (fun x ↦ (x.1, q x.1 x.2)) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]; rfl
      _ = U.map C ⊗ₘ lawK q := by
        rw [(indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).1 hind,
          map_subAt, map_prod_eq_compProd hq]

/-- `hasCondDistrib_fresh` for a program known to realize a kernel. -/
theorem hasCondDistrib_fresh' {C : Table → X} (hC : Measurable C) {S : Set Addr}
    (hCS : DependsOn C S) {pre : Addr} (hpre : ∀ a ∈ S, ¬ pre <+: a) {q : X → Src α}
    {κ : Kernel X α} (hq : Realizes q κ) :
    HasCondDistrib (fun ω ↦ q (C ω) (subAt pre ω)) C κ U := by
  rw [← hq.lawK_eq]
  exact hasCondDistrib_fresh hC hCS hpre hq.measurable

/-- **The key lemma, for a single draw.** A value computed from `C` and from an entry `a` of the
table that `C` never reads has, given `C`, the law `κ`, as soon as `f x` turns a uniform number
into a draw from `κ x`. -/
theorem hasCondDistrib_entry {C : Table → X} (hC : Measurable C) {S : Set Addr}
    (hCS : DependsOn C S) {a : Addr} (ha : a ∉ S) {f : X → I → α} (hf : Measurable (uncurry f))
    {κ : Kernel X α} [IsMarkovKernel κ] (hκ : ∀ x, volume.map (f x) = κ x) :
    HasCondDistrib (fun ω ↦ f (C ω) (ω a)) C κ U where
  aemeasurable := (hC.prodMk (hf.comp (hC.prodMk (measurable_pi_apply a)))).aemeasurable
  map_eq := by
    have hind : IndepFun C (fun ω ↦ ω a) U :=
      indepFun_of_dependsOn hC (measurable_pi_apply a) hCS (T := {a})
        (fun _ _ h ↦ h a rfl) (Set.disjoint_singleton_right.mpr ha)
    calc U.map (fun ω ↦ (C ω, f (C ω) (ω a)))
      _ = (U.map fun ω ↦ (C ω, ω a)).map (fun p ↦ (p.1, f p.1 p.2)) := by
        have hf' : Measurable fun p : X × I ↦ (p.1, f p.1 p.2) := measurable_fst.prodMk hf
        rw [Measure.map_map hf' (hC.prodMk (measurable_pi_apply a))]; rfl
      _ = U.map C ⊗ₘ κ := by
        rw [(indepFun_iff_map_prod_eq_prod_map_map hC.aemeasurable
          (measurable_pi_apply a).aemeasurable).1 hind,
          map_eval, map_prod_eq_compProd' hf hκ]

/-- `hasCondDistrib_entry` for the draw `sample κ` itself. -/
theorem hasCondDistrib_sampler [StandardBorelSpace α] [Nonempty α] {C : Table → X}
    (hC : Measurable C) {S : Set Addr} (hCS : DependsOn C S) {a : Addr} (ha : a ∉ S)
    (κ : Kernel X α) [IsMarkovKernel κ] :
    HasCondDistrib (fun ω ↦ sampler κ (C ω) (ω a)) C κ U :=
  hasCondDistrib_entry hC hCS ha (measurable_sampler κ) (map_sampler κ)

end Fresh

/-! ### Loops -/

section Loops

variable {ι St : Type} [MeasurableSpace St]

section Generic

variable {m : (α : Type) → [MeasurableSpace α] → Type} [MeasurableSpaceMonad m]

/-- A `for` loop over a list, as a plain structural recursion: run the body, then either stop or
carry on with the rest of the list. -/
def listLoop (g : ι → St → m (ForInStep St)) : List ι → St → m St
  | [], b => mPure b
  | a :: l, b => g a b >>=ₘ fun step ↦
      ForInStep.casesOn (motive := fun _ ↦ m St) step mPure fun b' ↦ listLoop g l b'

lemma loop_eq_listLoop (g : ι → St → m (ForInStep St)) :
    ∀ (l : List ι) (b : St) (as : List ι) (f : (a : ι) → a ∈ as → St → m (ForInStep St))
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

/-- The `for` loop of `rdo`, for any monad, is `listLoop`. -/
lemma forIn_eq_listLoop (l : List ι) (b : St) (g : ι → St → m (ForInStep St)) :
    MeasurableSpaceForIn.forIn (m := m) l b g = listLoop g l b :=
  loop_eq_listLoop g l b l _ (fun _ _ _ ↦ rfl) ⟨[], rfl⟩

end Generic

variable {γ : Type} [MeasurableSpace γ]

lemma Realizes.congr {α : Type} [MeasurableSpace α] {p p' : γ → Src α} {μ μ' : γ → Measure α}
    (h : Realizes p μ) (hp : ∀ c, p' c = p c) (hμ : ∀ c, μ' c = μ c) : Realizes p' μ' := by
  obtain rfl : p' = p := funext hp
  obtain rfl : μ' = μ := funext hμ
  exact h

lemma Realizes.listLoop {f : γ → ι → St → Src (ForInStep St)}
    {g : γ → ι → St → Measure (ForInStep St)} :
    ∀ (l : List ι), (∀ a ∈ l, Realizes (fun x : γ × St ↦ f x.1 a x.2) (fun x ↦ g x.1 a x.2)) →
      Realizes (fun x : γ × St ↦ RandomSource.listLoop (f x.1) l x.2)
        (fun x ↦ RandomSource.listLoop (g x.1) l x.2)
  | [], _ => by simpa only [RandomSource.listLoop] using Realizes.pure measurable_snd
  | a :: l, hf => by
    simp only [RandomSource.listLoop]
    refine Realizes.bind (hf a List.mem_cons_self) ?_
    have ih := (Realizes.listLoop l fun a' ha' ↦ hf a' (List.mem_cons_of_mem a ha')).comp
      (g := fun y : (γ × St) × ForInStep St ↦ (y.1.1, y.2.run)) (by fun_prop)
    refine (Realizes.ite (P := fun y : (γ × St) × ForInStep St ↦ y.2.isDone = true)
      ((ForInStep.measurable_isDone.comp measurable_snd) (measurableSet_singleton true))
      (Realizes.pure (ForInStep.measurable_run.comp measurable_snd)) ih).congr ?_ ?_
    · rintro ⟨x, s | s⟩ <;> rfl
    · rintro ⟨x, s | s⟩ <;> rfl

/-- **Loops.** -/
lemma Realizes.forIn {l : List ι} {b : γ → St} (hb : Measurable b)
    {f : γ → ι → St → Src (ForInStep St)} {g : γ → ι → St → Measure (ForInStep St)}
    (hf : ∀ a ∈ l, Realizes (fun x : γ × St ↦ f x.1 a x.2) (fun x ↦ g x.1 a x.2)) :
    Realizes (fun c ↦ MeasurableSpaceForIn.forIn (m := Src) l (b c) (f c))
      (fun c ↦ MeasurableSpaceForIn.forIn (m := Measure) l (b c) (g c)) := by
  simp only [forIn_eq_listLoop]
  exact (Realizes.listLoop l hf).comp (g := fun c ↦ (c, b c)) (measurable_id.prodMk hb)

end Loops

/-! ### Writing programs for any monad with `sample` -/

section Generic

variable {m : (α : Type) → [MeasurableSpace α] → Type} [MeasurableSpaceMonad m] [HasSample m]

/-- Draw from a fixed distribution. -/
def draw {α : Type} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α] (μ : Measure α)
    [IsProbabilityMeasure μ] : m α :=
  HasSample.sample (Kernel.const Unit μ) ()

end Generic

lemma Realizes.draw {γ α : Type} [MeasurableSpace γ] [MeasurableSpace α] [StandardBorelSpace α]
    [Nonempty α] (μ : Measure α) [IsProbabilityMeasure μ] :
    Realizes (fun _ : γ ↦ (draw μ : Src α)) (fun _ ↦ (draw μ : Measure α)) :=
  (Realizes.sample _).comp measurable_const

/-- Prove `Realizes` for a program built from `return`, `←`, `if`, `for` over a list, `sample` and
`draw`, one construct at a time. This is the analogue of `rdo_trace`, but it only has to check that each
construct is realized: the random variables themselves come for free, from running the program. -/
macro "realize" : tactic => `(tactic| repeat' first
  | exact Realizes.pure (by fun_prop)
  | exact Realizes.draw _
  | exact Realizes.sample _
  | exact (Realizes.sample _).comp (by fun_prop)
  | (refine Realizes.bind ?_ ?_ <;> beta_reduce)
  | (refine Realizes.ite (by measurability) ?_ ?_)
  | (refine Realizes.forIn (by fun_prop) ?_; intro _ _; beta_reduce))

/-! ## Example 1: two independent draws

```
rdo
  let x ← gaussianReal 0 1     -- reads the entry at [0]
  let y ← gaussianReal 0 1     -- reads the entry at [1, 0]
  return x + y
```
-/

section SumTwo

variable {m : (α : Type) → [MeasurableSpace α] → Type} [MeasurableSpaceMonad m] [HasSample m]

/-- Two independent standard Gaussians, added: written once for any monad that can sample. -/
def sumTwo : m ℝ := rdo
  let x ← draw (gaussianReal 0 1)
  let y ← draw (gaussianReal 0 1)
  return x + y

/-- The sampler of the standard Gaussian. -/
abbrev gauss : I → ℝ := sampler (Kernel.const Unit (gaussianReal 0 1)) ()

/-- The first draw, as a random variable: it reads the entry at `[0]`. -/
def X (ω : Table) : ℝ := gauss (ω [0])

/-- The second draw: it reads the entry at `[1, 0]`. -/
def Y (ω : Table) : ℝ := gauss (ω [1, 0])

/-- At `m := Src`, the program *is* `X + Y`, by definition. -/
lemma sumTwo_src (ω : Table) : sumTwo (m := Src) ω = X ω + Y ω := rfl

lemma hasLaw_X : HasLaw X (gaussianReal 0 1) U := hasLaw_sampler _ () [0]

lemma hasLaw_Y : HasLaw Y (gaussianReal 0 1) U := hasLaw_sampler _ () [1, 0]

lemma indepFun_X_Y : IndepFun X Y U :=
  indepFun_of_dependsOn (S := {[0]}) (T := {[1, 0]}) (by unfold X; fun_prop) (by unfold Y; fun_prop)
    (fun _ _ h ↦ by simp [X, h [0] rfl]) (fun _ _ h ↦ by simp [Y, h [1, 0] rfl]) (by simp)

lemma realizes_sumTwo :
    Realizes (fun _ : Unit ↦ sumTwo (m := Src)) (fun _ ↦ sumTwo (m := Measure)) := by
  unfold sumTwo; realize

/-- `X + Y` has the law of the program. -/
lemma hasLaw_X_add_Y : HasLaw (fun ω ↦ X ω + Y ω) (sumTwo (m := Measure)) U where
  aemeasurable := by unfold X Y; fun_prop
  map_eq := realizes_sumTwo.map_eq ()

end SumTwo

/-! ## Example 2: a chain of dependent draws

```
rdo
  let x ← κ c                 -- reads [0]
  let y ← η (c, x)            -- reads [1, 0]
  let z ← θ ((c, x), y)       -- reads [1, 1, 0]
  return x + y + z
```
-/

section Chain

variable {m : (α : Type) → [MeasurableSpace α] → Type} [MeasurableSpaceMonad m] [HasSample m]
  (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (η : Kernel (ℝ × ℝ) ℝ) [IsMarkovKernel η]
  (θ : Kernel ((ℝ × ℝ) × ℝ) ℝ) [IsMarkovKernel θ]

/-- `chain` of `RandomDo.Probability.Examples`, for any monad that can sample: at
`m := Measure` it is that program. -/
def chain (c : ℝ) : m ℝ := rdo
  let x ← HasSample.sample κ c
  let y ← HasSample.sample η (c, x)
  let z ← HasSample.sample θ ((c, x), y)
  return x + y + z


variable (c : ℝ)

/-- The three draws, as random variables. Each one reads its own entry, and is computed from the
draws before it. -/
def CX (ω : Table) : ℝ := sampler κ c (ω [0])
def CY (ω : Table) : ℝ := sampler η (c, CX κ c ω) (ω [1, 0])
def CZ (ω : Table) : ℝ := sampler θ ((c, CX κ c ω), CY κ η c ω) (ω [1, 1, 0])

lemma chain_src (ω : Table) :
    chain (m := Src) κ η θ c ω = CX κ c ω + CY κ η c ω + CZ κ η θ c ω := rfl

@[fun_prop] lemma measurable_CX : Measurable (CX κ c) := by unfold CX; fun_prop
@[fun_prop] lemma measurable_CY : Measurable (CY κ η c) := by
  unfold CY; exact measurable_sampler' _ (by fun_prop) (by fun_prop)
@[fun_prop] lemma measurable_CZ : Measurable (CZ κ η θ c) := by
  unfold CZ
  exact measurable_sampler' _ (by fun_prop) (by fun_prop)

/-- The first draw has law `κ c`. -/
lemma hasLaw_CX : HasLaw (CX κ c) (κ c) U := hasLaw_sampler κ c [0]

/-- Given the first draw `x`, the second has law `η (c, x)`. -/
lemma hasCondDistrib_CY :
    HasCondDistrib (CY κ η c) (CX κ c) (η.comap (fun x : ℝ ↦ (c, x)) measurable_prodMk_left) U :=
  hasCondDistrib_fresh' (S := {[0]}) (pre := [1, 0]) (measurable_CX κ c)
    (fun _ _ h ↦ by simp [CX, h [0] rfl]) (by simp)
    (q := fun x ↦ HasSample.sample (m := Src) η (c, x))
    ((Realizes.sample η).comp (g := fun x : ℝ ↦ (c, x)) (by fun_prop))

/-- Given the first two draws `(x, y)`, the third has law `θ ((c, x), y)`. -/
lemma hasCondDistrib_CZ :
    HasCondDistrib (CZ κ η θ c) (fun ω ↦ (CX κ c ω, CY κ η c ω))
      (θ.comap (fun p : ℝ × ℝ ↦ ((c, p.1), p.2))
        ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)) U :=
  hasCondDistrib_fresh' (S := {[0], [1, 0]}) (pre := [1, 1, 0])
    ((measurable_CX κ c).prodMk (measurable_CY κ η c))
    (fun _ _ h ↦ by simp [CX, CY, h [0] (by simp), h [1, 0] (by simp)]) (by simp)
    (q := fun p ↦ HasSample.sample (m := Src) θ ((c, p.1), p.2))
    ((Realizes.sample θ).comp (g := fun p : ℝ × ℝ ↦ ((c, p.1), p.2)) (by fun_prop))

lemma realizes_chain : Realizes (chain (m := Src) κ η θ) (chain (m := Measure) κ η θ) := by
  unfold chain; realize

/-- The result has the law of the program. -/
lemma hasLaw_chain :
    HasLaw (fun ω ↦ CX κ c ω + CY κ η c ω + CZ κ η θ c ω) (chain (m := Measure) κ η θ c) U where
  aemeasurable := by fun_prop
  map_eq := (realizes_chain κ η θ).map_eq c

end Chain

/-! ## Example 3: a loop with a branch

```
rdo
  let mut S := 0
  for _ in List.replicate n () rdo      -- iteration k reads the part under 0 :: 1ᵏ ++ [0]
    let b ← fairCoin                     --   the coin: its entry [0]
    if b then
      let z ← gaussianReal 0 1           --   the Gaussian: its entry [1, 0]
      S := S + z
  return S
```

The Gaussian of iteration `k` is only *drawn* when the coin says heads, but the entry it would
read is there either way, so `Z k` below is a random variable on the whole space. The program is
`∑ₖ 1{B k} Z k` (`coinSum_src`), and each `Z k` is standard Gaussian *given the coin and
everything before it* (`hasCondDistrib_Z`) — including on the event where the branch is not
taken. No case analysis on the branch is needed anywhere.
-/

section CoinSum

variable {m : (α : Type) → [MeasurableSpace α] → Type} [MeasurableSpaceMonad m] [HasSample m]

/-- The fair coin. -/
def fairCoin : Measure Bool := bernoulliMeasure true false ⟨1 / 2, by norm_num, by norm_num⟩

instance : IsProbabilityMeasure fairCoin := by unfold fairCoin; infer_instance

/-- Flip `n` coins, and add a standard Gaussian for each heads. -/
def coinSum (n : ℕ) : m ℝ := rdo
  let mut S := 0
  for _ in List.replicate n () rdo
    let b ← draw fairCoin
    if b then
      let z ← draw (gaussianReal 0 1)
      S := S + z
  return S

lemma realizes_coinSum (n : ℕ) :
    Realizes (fun _ : Unit ↦ coinSum (m := Src) n) (fun _ ↦ coinSum (m := Measure) n) := by
  unfold coinSum; realize

/-- The body of the loop, as `rdo` elaborates it. -/
def coinBody (S : ℝ) : m (ForInStep ℝ) :=
  draw fairCoin >>=ₘ fun b ↦
    if b = true then draw (gaussianReal 0 1) >>=ₘ fun z ↦ mPure (ForInStep.yield (S + z))
    else mPure (ForInStep.yield S)

lemma coinSum_eq (n : ℕ) :
    coinSum (m := m) n
      = MeasurableSpaceForIn.forIn (List.replicate n ()) (0 : ℝ) (fun _ S ↦ coinBody S)
          >>=ₘ fun S ↦ mPure S := rfl

/-- The sampler of the fair coin. -/
abbrev coin : I → Bool := sampler (Kernel.const Unit fairCoin) ()

lemma coinBody_src (S : ℝ) (ω : Table) :
    coinBody (m := Src) S ω
      = ForInStep.yield (S + if coin (ω [0]) then gauss (ω [1, 0]) else 0) := by
  change (if coin (ω [0]) = true then
      (draw (gaussianReal 0 1) >>=ₘ fun z ↦ mPure (ForInStep.yield (S + z)) : Src _)
    else mPure (ForInStep.yield S)) (subAt [1] ω) = _
  cases coin (ω [0]) <;> simp <;> rfl

lemma forIn_coinBody (n : ℕ) : ∀ (S : ℝ) (ω : Table),
    MeasurableSpaceForIn.forIn (m := Src) (List.replicate n ()) S (fun _ S ↦ coinBody S) ω
      = S + ∑ k ∈ Finset.range n, if coin (ω (List.replicate k 1 ++ [0, 0]))
          then gauss (ω (List.replicate k 1 ++ [0, 1, 0])) else 0 := by
  simp only [forIn_eq_listLoop]
  induction n with
  | zero => intro S ω; simp only [Finset.range_zero, Finset.sum_empty, add_zero]; rfl
  | succ n ih =>
    intro S ω
    change ForInStep.casesOn (motive := fun _ ↦ Src ℝ) (coinBody (m := Src) S (subAt [0] ω))
      mPure (fun S' ↦ listLoop (fun _ S ↦ coinBody S) (List.replicate n ()) S') (subAt [1] ω) = _
    rw [coinBody_src]
    change listLoop (m := Src) _ _ _ (subAt [1] ω) = _
    rw [ih, Finset.sum_range_succ']
    simp only [subAt, List.replicate_succ, List.cons_append, List.replicate_zero, List.nil_append]
    exact (add_assoc _ _ _).trans (congrArg (S + ·) (add_comm _ _))

/-- Where iteration `k` of the loop reads: the loop sits under `[0]`, and each iteration hands
the rest of the loop the part under `[1]`. -/
def iterAddr (k : ℕ) (t : Addr) : Addr := 0 :: (List.replicate k 1 ++ 0 :: t)

lemma iterAddr_inj {j k : ℕ} {t t' : Addr} (h : iterAddr j t = iterAddr k t') : j = k ∧ t = t' := by
  simp only [iterAddr, List.cons.injEq, true_and] at h
  induction j generalizing k with
  | zero => cases k <;> simp_all [List.replicate_succ]
  | succ j ih =>
    cases k with
    | zero => simp [List.replicate_succ] at h
    | succ k =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      simpa using ih h

/-- The coin of iteration `k`. -/
def B (k : ℕ) (ω : Table) : Bool := coin (ω (iterAddr k [0]))

/-- The Gaussian of iteration `k`: a random variable whether or not the branch draws it. -/
def Z (k : ℕ) (ω : Table) : ℝ := gauss (ω (iterAddr k [1, 0]))

/-- **The program, pathwise.** -/
theorem coinSum_src (n : ℕ) (ω : Table) :
    coinSum (m := Src) n ω = ∑ k ∈ Finset.range n, if B k ω then Z k ω else 0 := by
  rw [coinSum_eq]
  change MeasurableSpaceForIn.forIn (m := Src) _ _ _ (subAt [0] ω) = _
  rw [forIn_coinBody, zero_add]
  rfl

@[fun_prop] lemma measurable_B (k : ℕ) : Measurable (B k) := by unfold B; fun_prop
@[fun_prop] lemma measurable_Z (k : ℕ) : Measurable (Z k) := by unfold Z; fun_prop

/-- Everything iterations `0, …, k-1` drew. -/
def Past (k : ℕ) (ω : Table) : Fin k → Bool × ℝ := fun j ↦ (B j ω, Z j ω)

@[fun_prop] lemma measurable_Past (k : ℕ) : Measurable (Past k) := by
  unfold Past; exact measurable_pi_iff.mpr fun j ↦ by fun_prop

/-- The entries iterations `0, …, k-1` read. -/
def pastAddrs (k : ℕ) : Set Addr := {a | ∃ j < k, ∃ t, a = iterAddr j t}

lemma dependsOn_Past (k : ℕ) : DependsOn (Past k) (pastAddrs k) := fun ω ω' h ↦ funext fun j ↦ by
  simp only [Past, B, Z, h _ ⟨j, j.2, _, rfl⟩]

lemma iterAddr_not_mem_pastAddrs (k : ℕ) (t : Addr) : iterAddr k t ∉ pastAddrs k := by
  rintro ⟨j, hj, t', h⟩
  exact (iterAddr_inj h).1 ▸ hj |>.false

/-- Given the past, the coin of iteration `k` is fair. -/
theorem hasCondDistrib_B (k : ℕ) :
    HasCondDistrib (B k) (Past k) (Kernel.const _ fairCoin) U :=
  hasCondDistrib_entry (measurable_Past k) (dependsOn_Past k) (iterAddr_not_mem_pastAddrs k [0])
    (f := fun _ u ↦ coin u) (by fun_prop) fun _ ↦ map_sampler _ ()

/-- Given the past *and the coin*, the Gaussian of iteration `k` is standard Gaussian. -/
theorem hasCondDistrib_Z (k : ℕ) :
    HasCondDistrib (Z k) (fun ω ↦ (Past k ω, B k ω)) (Kernel.const _ (gaussianReal 0 1)) U := by
  refine hasCondDistrib_entry ((measurable_Past k).prodMk (measurable_B k))
    (S := pastAddrs k ∪ {iterAddr k [0]}) ?_ ?_ (f := fun _ u ↦ gauss u) (by fun_prop)
    fun _ ↦ map_sampler _ ()
  · intro ω ω' h
    simp only [Prod.mk.injEq]
    exact ⟨dependsOn_Past k fun a ha ↦ h a (Or.inl ha), by simp [B, h _ (Or.inr rfl)]⟩
  · rintro (h | h)
    · exact iterAddr_not_mem_pastAddrs k _ h
    · simpa using (iterAddr_inj h).2

/-- In particular the Gaussian is independent of the coin and of the past. -/
example (k : ℕ) : IndepFun (fun ω ↦ (Past k ω, B k ω)) (Z k) U :=
  (hasCondDistrib_Z k).indepFun_of_const

/-- And `∑ₖ 1{B k} Z k` has the law of the program. -/
theorem hasLaw_coinSum (n : ℕ) :
    HasLaw (fun ω ↦ ∑ k ∈ Finset.range n, if B k ω then Z k ω else 0) (coinSum (m := Measure) n) U
    where
  aemeasurable := by
    refine (Finset.measurable_sum _ fun k _ ↦ ?_).aemeasurable
    exact Measurable.ite ((measurable_B k) (measurableSet_singleton true)) (measurable_Z k)
      measurable_const
  map_eq := by
    rw [← (realizes_coinSum n).map_eq ()]
    exact congrArg (U.map ·) (funext fun ω ↦ (coinSum_src n ω).symm)

end CoinSum

/-! ## Example 4: an algorithm interacting with an environment

An algorithm and an environment are given by table programs, one per round: the observation, the
action and the feedback of round `n`, each from the history so far. Their laws, `lawK`, make them
a LeanMachineLearning `Algorithm` and `Environment`.

The interaction runs them against the table, round `n` reading the part under `[n]`: the
observation under `[n, 0]`, the action under `[n, 1]` and the feedback under `[n, 2]`. The rounds
are indexed by their number, not by their position in a program, so the random variables `O n`,
`A n`, `Y n` are the same whatever the horizon.

`isAlgEnvSeq` is then three applications of `hasCondDistrib_fresh`: each of the three reads a part
of the table that the history (and the observation, and the action) never read. Nothing in the
proof looks inside the programs, so it holds for arbitrary algorithms and environments, with any
branches, loops or recursion inside a round.
-/

namespace Interaction

open Learning

variable {𝓞 𝓐 𝓨 : Type} [MeasurableSpace 𝓞] [MeasurableSpace 𝓐] [MeasurableSpace 𝓨]

/-- An algorithm given by table programs. -/
structure SrcAlg (𝓞 𝓐 𝓨 : Type) [MeasurableSpace 𝓞] [MeasurableSpace 𝓐] [MeasurableSpace 𝓨] where
  /-- The action of round `n`, from the history and the observation. -/
  policy (n : ℕ) : Hist 𝓞 𝓐 𝓨 n × 𝓞 → Src 𝓐
  measurable (n : ℕ) : Measurable fun x : (Hist 𝓞 𝓐 𝓨 n × 𝓞) × Table ↦ policy n x.1 x.2

/-- An environment given by table programs. -/
structure SrcEnv (𝓞 𝓐 𝓨 : Type) [MeasurableSpace 𝓞] [MeasurableSpace 𝓐] [MeasurableSpace 𝓨] where
  /-- The observation of round `n`, from the history. -/
  obs (n : ℕ) : Hist 𝓞 𝓐 𝓨 n → Src 𝓞
  /-- The feedback of round `n`, from the history, the observation and the action. -/
  feedback (n : ℕ) : (Hist 𝓞 𝓐 𝓨 n × 𝓞) × 𝓐 → Src 𝓨
  measurable_obs (n : ℕ) : Measurable fun x : Hist 𝓞 𝓐 𝓨 n × Table ↦ obs n x.1 x.2
  measurable_feedback (n : ℕ) :
    Measurable fun x : ((Hist 𝓞 𝓐 𝓨 n × 𝓞) × 𝓐) × Table ↦ feedback n x.1 x.2

/-- The algorithm, as a LeanMachineLearning algorithm: the laws of its programs. -/
def SrcAlg.toAlgorithm (alg : SrcAlg 𝓞 𝓐 𝓨) : Algorithm 𝓞 𝓐 𝓨 where
  policy n := lawK (alg.policy n)
  isMarkovKernel_policy n := isMarkovKernel_lawK (alg.measurable n)

/-- The environment, as a LeanMachineLearning environment. -/
def SrcEnv.toEnvironment (env : SrcEnv 𝓞 𝓐 𝓨) : Environment 𝓞 𝓐 𝓨 where
  obs n := lawK (env.obs n)
  feedback n := lawK (env.feedback n)
  isMarkovKernel_obs n := isMarkovKernel_lawK (env.measurable_obs n)
  isMarkovKernel_feedback n := isMarkovKernel_lawK (env.measurable_feedback n)

/-- When the programs realize kernels, those kernels are the policy. -/
lemma SrcAlg.toAlgorithm_policy (alg : SrcAlg 𝓞 𝓐 𝓨) {n : ℕ}
    {κ : Kernel (Hist 𝓞 𝓐 𝓨 n × 𝓞) 𝓐} (h : Realizes (alg.policy n) κ) :
    alg.toAlgorithm.policy n = κ := h.lawK_eq

variable (alg : SrcAlg 𝓞 𝓐 𝓨) (env : SrcEnv 𝓞 𝓐 𝓨)

/-- One round, given the history so far. -/
def playRound (n : ℕ) (h : Hist 𝓞 𝓐 𝓨 n) (ω : Table) : Round 𝓞 𝓐 𝓨 :=
  let o := env.obs n h (subAt [n, 0] ω)
  let a := alg.policy n (h, o) (subAt [n, 1] ω)
  (o, a, env.feedback n ((h, o), a) (subAt [n, 2] ω))

/-- Round `n` of the interaction, run against the table. -/
def round (n : ℕ) (ω : Table) : Round 𝓞 𝓐 𝓨 := playRound alg env n (fun i : Fin n ↦ round i ω) ω
termination_by n
decreasing_by exact i.2

/-- The observations, actions and feedbacks of the interaction. -/
def O (n : ℕ) (ω : Table) : 𝓞 := (round alg env n ω).1
def A (n : ℕ) (ω : Table) : 𝓐 := (round alg env n ω).2.1
def Y (n : ℕ) (ω : Table) : 𝓨 := (round alg env n ω).2.2

/-- The history of the interaction. -/
abbrev H (n : ℕ) : Table → Hist 𝓞 𝓐 𝓨 n := history (O alg env) (A alg env) (Y alg env) n

lemma H_apply (n : ℕ) (ω : Table) : H alg env n ω = fun i : Fin n ↦ round alg env i ω := rfl

lemma O_eq (n : ℕ) : O alg env n = fun ω ↦ env.obs n (H alg env n ω) (subAt [n, 0] ω) := by
  funext ω; rw [O, round]; rfl

lemma A_eq (n : ℕ) :
    A alg env n = fun ω ↦ alg.policy n (H alg env n ω, O alg env n ω) (subAt [n, 1] ω) := by
  funext ω; rw [A, round, O, round]; rfl

lemma Y_eq (n : ℕ) : Y alg env n
    = fun ω ↦ env.feedback n ((H alg env n ω, O alg env n ω), A alg env n ω) (subAt [n, 2] ω) := by
  funext ω; rw [Y, round, O, round, A, round]; rfl

lemma measurable_playRound (n : ℕ) :
    Measurable fun x : Hist 𝓞 𝓐 𝓨 n × Table ↦ playRound alg env n x.1 x.2 := by
  have ho : Measurable fun x : Hist 𝓞 𝓐 𝓨 n × Table ↦ env.obs n x.1 (subAt [n, 0] x.2) :=
    (env.measurable_obs n).comp (measurable_fst.prodMk ((measurable_subAt _).comp measurable_snd))
  have ha : Measurable fun x : Hist 𝓞 𝓐 𝓨 n × Table ↦
      alg.policy n (x.1, env.obs n x.1 (subAt [n, 0] x.2)) (subAt [n, 1] x.2) :=
    (alg.measurable n).comp ((measurable_fst.prodMk ho).prodMk
      ((measurable_subAt _).comp measurable_snd))
  exact ho.prodMk (ha.prodMk ((env.measurable_feedback n).comp
    (((measurable_fst.prodMk ho).prodMk ha).prodMk ((measurable_subAt _).comp measurable_snd))))

lemma measurable_round (n : ℕ) : Measurable (round alg env n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hH : Measurable fun ω ↦ fun i : Fin n ↦ round alg env i ω :=
      measurable_pi_iff.mpr fun i ↦ ih i i.2
    have : round alg env n = fun ω ↦ playRound alg env n (fun i : Fin n ↦ round alg env i ω) ω := by
      funext ω; rw [round]
    rw [this]
    exact (measurable_playRound alg env n).comp (hH.prodMk measurable_id)

@[fun_prop] lemma measurable_O (n : ℕ) : Measurable (O alg env n) :=
  measurable_fst.comp (measurable_round alg env n)
@[fun_prop] lemma measurable_A (n : ℕ) : Measurable (A alg env n) :=
  measurable_fst.comp (measurable_snd.comp (measurable_round alg env n))
@[fun_prop] lemma measurable_Y (n : ℕ) : Measurable (Y alg env n) :=
  measurable_snd.comp (measurable_snd.comp (measurable_round alg env n))
@[fun_prop] lemma measurable_H (n : ℕ) : Measurable (H alg env n) :=
  measurable_history (measurable_O alg env) (measurable_A alg env) (measurable_Y alg env) n

/-- The entries read by rounds `0, …, n-1`. -/
def before (n : ℕ) : Set Addr := {a | ∃ j < n, ∃ t, a = j :: t}

/-- The entries read by round `n` for its observation (`i = 0`), action (`1`), feedback (`2`). -/
def part (n i : ℕ) : Set Addr := {a | ∃ t, a = n :: i :: t}

lemma subAt_eq_of_eqOn {n i : ℕ} {ω ω' : Table} (h : ∀ a ∈ part n i, ω a = ω' a) :
    subAt [n, i] ω = subAt [n, i] ω' :=
  funext fun t ↦ h _ ⟨t, rfl⟩

lemma dependsOn_round (n : ℕ) : DependsOn (round alg env n) (before (n + 1)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ω ω' h
    have hH : (fun i : Fin n ↦ round alg env i ω) = fun i : Fin n ↦ round alg env i ω' :=
      funext fun i : Fin n ↦ ih i i.2 fun a ⟨j, hj, t, ha⟩ ↦ h a ⟨j, by have := i.2; omega, t, ha⟩
    have hp (i : ℕ) : subAt [n, i] ω = subAt [n, i] ω' :=
      subAt_eq_of_eqOn fun a ⟨t, ha⟩ ↦ h a ⟨n, by omega, i :: t, ha⟩
    rw [round, round, hH]
    simp only [playRound, hp]

lemma dependsOn_H (n : ℕ) : DependsOn (H alg env n) (before n) := fun ω ω' h ↦ by
  rw [H_apply, H_apply]
  exact funext fun i : Fin n ↦ dependsOn_round alg env i fun a ⟨j, hj, t, ha⟩ ↦
    h a ⟨j, by have := i.2; omega, t, ha⟩

lemma dependsOn_HO (n : ℕ) :
    DependsOn (fun ω ↦ (H alg env n ω, O alg env n ω)) (before n ∪ part n 0) := by
  intro ω ω' h
  have hH := dependsOn_H alg env n fun a ha ↦ h a (Or.inl ha)
  rw [O_eq]
  simp only [hH, subAt_eq_of_eqOn fun a ha ↦ h a (Or.inr ha)]

lemma dependsOn_HOA (n : ℕ) :
    DependsOn (fun ω ↦ ((H alg env n ω, O alg env n ω), A alg env n ω))
      (before n ∪ part n 0 ∪ part n 1) := by
  intro ω ω' h
  have hHO := dependsOn_HO alg env n fun a ha ↦ h a (Or.inl ha)
  simp only [Prod.mk.injEq] at hHO
  rw [A_eq]
  simp only [hHO, subAt_eq_of_eqOn fun a ha ↦ h a (Or.inr ha)]

lemma not_prefix_before {n i : ℕ} : ∀ a ∈ before n, ¬ [n, i] <+: a := by
  rintro _ ⟨j, hj, t, rfl⟩ ⟨u, hu⟩
  simp only [List.cons_append, List.cons.injEq] at hu
  omega

lemma not_prefix_part {n i k : ℕ} (hik : i ≠ k) : ∀ a ∈ part n k, ¬ [n, i] <+: a := by
  rintro _ ⟨t, rfl⟩ ⟨u, hu⟩
  simp only [List.cons_append, List.cons.injEq] at hu
  omega

/-- **The interaction is an algorithm-environment sequence**, for any algorithm and environment
given by table programs. -/
theorem isAlgEnvSeq :
    IsAlgEnvSeq (O alg env) (A alg env) (Y alg env) alg.toAlgorithm env.toEnvironment U where
  measurable_obs := measurable_O alg env
  measurable_action := measurable_A alg env
  measurable_feedback := measurable_Y alg env
  hasCondDistrib_obs n := by
    rw [O_eq]
    exact hasCondDistrib_fresh (measurable_H alg env n) (dependsOn_H alg env n) not_prefix_before
      (env.measurable_obs n)
  hasCondDistrib_action n := by
    rw [A_eq]
    refine hasCondDistrib_fresh ((measurable_H alg env n).prodMk (measurable_O alg env n))
      (dependsOn_HO alg env n) ?_ (alg.measurable n)
    rintro a (ha | ha)
    · exact not_prefix_before a ha
    · exact not_prefix_part (by decide) a ha
  hasCondDistrib_feedback n := by
    rw [Y_eq]
    refine hasCondDistrib_fresh (((measurable_H alg env n).prodMk (measurable_O alg env n)).prodMk
      (measurable_A alg env n)) (dependsOn_HOA alg env n) ?_ (env.measurable_feedback n)
    rintro a ((ha | ha) | ha)
    · exact not_prefix_before a ha
    · exact not_prefix_part (by decide) a ha
    · exact not_prefix_part (by decide) a ha

/-! ### ε-greedy against two Gaussian arms

The same interaction, for a concrete algorithm written in `rdo`. Its internal draws — the
exploration coin and the uniform arm — are entries of the table, so they are random variables on
the space carrying the `IsAlgEnvSeq`, with no further construction.
-/

section EpsGreedy

variable {m : (α : Type) → [MeasurableSpace α] → Type} [MeasurableSpaceMonad m] [HasSample m]

/-- The arm played last, or `true` before the first round. -/
def lastAction : (n : ℕ) → Hist Unit Bool ℝ n → Bool
  | 0, _ => true
  | n + 1, h => (h (Fin.last n)).2.1

@[fun_prop] lemma measurable_lastAction (n : ℕ) : Measurable (lastAction n) := by
  cases n with
  | zero => exact measurable_const
  | succ n => exact (measurable_pi_apply (Fin.last n)).snd.fst

variable (ε : I)

/-- ε-greedy with two arms: with probability `ε` play a uniformly random arm, otherwise replay the
last one. The policy of round `n` reads the history and the (trivial) observation. -/
def epsPolicy (n : ℕ) (x : Hist Unit Bool ℝ n × Unit) : m Bool := rdo
  let explore ← draw (bernoulliMeasure true false ε)
  if explore then
    let u ← draw fairCoin
    return u
  else
    return lastAction n x.1

lemma realizes_epsPolicy (n : ℕ) :
    Realizes (epsPolicy (m := Src) ε n) (epsPolicy (m := Measure) ε n) := by
  unfold epsPolicy; realize

variable (μ : Bool → ℝ)

/-- Two Gaussian arms with means `μ true` and `μ false`. -/
def arms : Kernel Bool ℝ := Kernel.ofFunOfCountable fun a ↦ gaussianReal (μ a) 1

instance : IsMarkovKernel (arms μ) := ⟨fun a ↦ by unfold arms; exact inferInstanceAs
  (IsProbabilityMeasure (gaussianReal (μ a) 1))⟩

/-- ε-greedy, as table programs. -/
def epsAlg : SrcAlg Unit Bool ℝ where
  policy n := epsPolicy (m := Src) ε n
  measurable n := (realizes_epsPolicy ε n).measurable

/-- The Gaussian arms, as table programs: no observation, and the reward of the arm played. -/
def gaussEnv : SrcEnv Unit Bool ℝ where
  obs _ _ := mPure ()
  feedback _ x := HasSample.sample (m := Src) (arms μ) x.2
  measurable_obs _ := measurable_const
  measurable_feedback n :=
    ((Realizes.sample (arms μ)).comp (g := fun x : (Hist Unit Bool ℝ n × Unit) × Bool ↦ x.2)
      measurable_snd).measurable

/-- The LeanMachineLearning algorithm is the `rdo` program. -/
lemma epsAlg_policy (n : ℕ) (x : Hist Unit Bool ℝ n × Unit) :
    (epsAlg ε).toAlgorithm.policy n x = epsPolicy (m := Measure) ε n x := by
  change lawK ((epsAlg ε).policy n) x = _
  rw [lawK_apply ((epsAlg ε).measurable n)]
  exact (realizes_epsPolicy ε n).map_eq x

theorem isAlgEnvSeq_eps :
    IsAlgEnvSeq (O (epsAlg ε) (gaussEnv μ)) (A (epsAlg ε) (gaussEnv μ)) (Y (epsAlg ε) (gaussEnv μ))
      (epsAlg ε).toAlgorithm (gaussEnv μ).toEnvironment U :=
  isAlgEnvSeq _ _

/-- The exploration coin of round `t`. -/
def Explore (t : ℕ) (ω : Table) : Bool :=
  sampler (Kernel.const Unit (bernoulliMeasure true false ε)) () (ω [t, 1, 0])

/-- The uniform arm of round `t`: a random variable whether or not round `t` explores. It reads
`[t, 1, 1]` rather than `[t, 1, 1, 0]` because `rdo` elaborates `let u ← draw fairCoin; return u`
to `draw fairCoin`: addresses follow the elaborated program. -/
def Unif (t : ℕ) (ω : Table) : Bool := coin (ω [t, 1, 1])

/-- **The action, pathwise.** -/
theorem A_eps (t : ℕ) (ω : Table) :
    A (epsAlg ε) (gaussEnv μ) t ω
      = if Explore ε t ω then Unif t ω else lastAction t (H (epsAlg ε) (gaussEnv μ) t ω) := by
  rw [A_eq]
  change (if Explore ε t ω = true then (draw fairCoin : Src Bool)
    else mPure (lastAction t (H (epsAlg ε) (gaussEnv μ) t ω))) (subAt [1] (subAt [t, 1] ω)) = _
  cases Explore ε t ω <;> rfl

/-- Given the history and the observation, round `t` explores with probability `ε`. -/
theorem hasCondDistrib_Explore (t : ℕ) :
    HasCondDistrib (Explore ε t)
      (fun ω ↦ (H (epsAlg ε) (gaussEnv μ) t ω, O (epsAlg ε) (gaussEnv μ) t ω))
      (Kernel.const _ (bernoulliMeasure true false ε)) U := by
  refine hasCondDistrib_entry ((measurable_H _ _ t).prodMk (measurable_O _ _ t))
    (dependsOn_HO _ _ t) ?_ (f := fun _ u ↦ sampler (Kernel.const Unit
      (bernoulliMeasure true false ε)) () u) (by fun_prop) fun _ ↦ map_sampler _ ()
  rintro (⟨j, hj, _, h⟩ | ⟨_, h⟩) <;> simp_all

/-- **Every arm is explored**: at every round, each arm is played with probability at least
`ε · ½`. The proof reads it off the pathwise form of the action: exploring and drawing `a`
are two independent entries of the table. -/
theorem le_map_A (t : ℕ) (a : Bool) :
    (unitInterval.toNNReal ε : ℝ≥0∞) * fairCoin {a} ≤ U.map (A (epsAlg ε) (gaussEnv μ) t) {a} := by
  have hE : Measurable (Explore ε t) := by unfold Explore; fun_prop
  have hU : Measurable (Unif t) := by unfold Unif; fun_prop
  have hind : IndepFun (Explore ε t) (Unif t) U :=
    indepFun_of_dependsOn hE hU (S := {[t, 1, 0]}) (T := {[t, 1, 1]})
      (fun _ _ h ↦ by simp [Explore, h _ rfl]) (fun _ _ h ↦ by simp [Unif, h _ rfl]) (by simp)
  have hlawE : U (Explore ε t ⁻¹' {true}) = unitInterval.toNNReal ε := by
    have hmap : U.map (Explore ε t) = bernoulliMeasure true false ε :=
      (hasLaw_sampler (Kernel.const Unit (bernoulliMeasure true false ε)) () [t, 1, 0]).map_eq
    rw [← Measure.map_apply hE (measurableSet_singleton _), hmap]
    exact bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton _) rfl (by simp)
  have hlawU : U (Unif t ⁻¹' {a}) = fairCoin {a} := by
    have hmap : U.map (Unif t) = fairCoin :=
      (hasLaw_sampler (Kernel.const Unit fairCoin) () [t, 1, 1]).map_eq
    rw [← Measure.map_apply hU (measurableSet_singleton _), hmap]
  rw [← hlawE, ← hlawU, ← (indepFun_iff_measure_inter_preimage_eq_mul.1 hind) _ _
      (measurableSet_singleton _) (measurableSet_singleton _),
    Measure.map_apply (measurable_A _ _ t) (measurableSet_singleton _)]
  refine measure_mono fun ω ⟨h₁, h₂⟩ ↦ ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at h₁ h₂ ⊢
  simp [A_eps, h₁, h₂]

/-- **The same bound on any space.** The law of the trajectory does not depend on the space, so
the bound proved on the table holds for every algorithm-environment sequence of ε-greedy. -/
theorem le_map_action {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {O' : ℕ → Ω → Unit} {A' : ℕ → Ω → Bool} {Y' : ℕ → Ω → ℝ}
    (h : IsAlgEnvSeq O' A' Y' (epsAlg ε).toAlgorithm (gaussEnv μ).toEnvironment P) (t : ℕ)
    (a : Bool) :
    (unitInterval.toNNReal ε : ℝ≥0∞) * fairCoin {a} ≤ P.map (A' t) {a} := by
  have hf : Measurable fun τ : ℕ → Round Unit Bool ℝ ↦ (τ t).2.1 := by fun_prop
  have key : P.map (A' t) = U.map (A (epsAlg ε) (gaussEnv μ) t) := by
    have := isAlgEnvSeq_unique h (isAlgEnvSeq_eps ε μ)
    rw [show A' t = (fun τ ↦ (τ t).2.1) ∘ trajectory O' A' Y' from rfl,
      show A (epsAlg ε) (gaussEnv μ) t = (fun τ ↦ (τ t).2.1)
        ∘ trajectory (O (epsAlg ε) (gaussEnv μ)) (A (epsAlg ε) (gaussEnv μ))
          (Y (epsAlg ε) (gaussEnv μ)) from rfl,
      ← Measure.map_map hf h.measurable_trajectory,
      ← Measure.map_map hf (isAlgEnvSeq_eps ε μ).measurable_trajectory, this]
  rw [key]
  exact le_map_A ε μ t a

end EpsGreedy

end Interaction

end RDo.RandomSource

end

end
