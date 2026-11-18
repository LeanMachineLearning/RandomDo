/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.MeasurableSpaceMonad.ForIn
public import RandomDo.MeasurableSpaceMonad.List
public import Std.Internal.ForIn.Lemmas

/-!
# List iteration on measurable spaces

This file defines the `MeasurableSpaceForIn'` instance for looping over `List`s in `rdo`
notation, together with its laws and measurability lemmas. It also implements the "internal" classes
`PureMeasurableSpaceForIn` and `PureMeasurableSpaceForIn'` which are the analogues of core Lean's
`Std.Internal.PureForIn` and `Std.Internal.PureForIn'`, and assert that iteration over the given
`MeasurableSpaceForIn` or `MeasurableSpaceForIn'` instance produces its elements without monadic
effects.
-/

@[expose] public section

open MeasureTheory

namespace List

universe u v w x

variable {α : Type w} {m : (α : Type u) → [MeasurableSpace α] → Type v}
  [MeasurableSpaceMonad m] {β γ : Type u} [MeasurableSpace β] [MeasurableSpace γ]

/-- Implementation of iteration over a `List`. Analogue of core's `List.forIn'`. -/
@[inline]
protected def mForIn' (as : @& List α) (init : β)
    (f : (a : α) → a ∈ as → β → m (ForInStep β)) : m β :=
  let rec @[specialize, nolint docBlame]
    loop : (as' : @& List α) → (b : β) → Exists (fun bs => bs ++ as' = as) → m β
      | [], b, _    => mPure b
      | a::as', b, h => rdo
        have : a ∈ as := by
          clear f
          have ⟨bs, h⟩ := h
          subst h
          exact mem_append_right _ (Mem.head ..)
        match (← f a this b) with
        | ForInStep.done b  => mPure b
        | ForInStep.yield b =>
          have : Exists (fun bs => bs ++ as' = as) :=
            have ⟨bs, h⟩ := h
            ⟨bs ++ [a], by rw [← h, append_cons (bs := as')]⟩
          loop as' b this
  loop as init ⟨[], rfl⟩

instance : MeasurableSpaceForIn' m (List α) α inferInstance where
  mForIn' := List.mForIn'

@[simp, grind =] theorem mForIn'_eq_mForIn' :
    List.mForIn' (m := m) (α := α) (β := β) = mForIn' := rfl

@[simp, grind =] theorem mForIn'_nil
    {f : (a : α) → a ∈ [] → β → m (ForInStep β)} {b : β} :
    mForIn' [] b f = mPure b := rfl

@[simp, grind =] theorem mForIn_nil {f : α → β → m (ForInStep β)} {b : β} :
    mForIn ([] : List α) b f = mPure b := rfl

theorem mForIn'_loop_congr {as bs xs : List α}
    {f : (a' : α) → a' ∈ as → β → m (ForInStep β)}
    {g : (a' : α) → a' ∈ bs → β → m (ForInStep β)}
    {b : β} (ha : ∃ ys, ys ++ xs = as) (hb : ∃ ys, ys ++ xs = bs)
    (h : ∀ a m m' b, f a m b = g a m' b) :
    mForIn'.loop as f xs b ha = mForIn'.loop bs g xs b hb := by
  induction xs generalizing b with
  | nil => simp [mForIn'.loop]
  | cons a xs ih =>
    simp only [mForIn'.loop] at *
    congr 1
    · rw [h]
    · funext s
      obtain b | b := s
      · rfl
      · dsimp only
        rw [ih]

@[simp, grind =] theorem mForIn'_cons {a : α} {as : List α}
    (f : (a' : α) → a' ∈ a :: as → β → m (ForInStep β)) (b : β) :
    mForIn' (a :: as) b f = f a mem_cons_self b >>=ₘ
      fun | ForInStep.done b => mPure b
          | ForInStep.yield b =>
            mForIn' as b fun a' h b => f a' (mem_cons_of_mem a h) b := by
  simp only [mForIn', List.mForIn', List.mForIn'.loop]
  congr 1
  funext s
  obtain b | b := s
  · rfl
  · apply mForIn'_loop_congr
    intros
    rfl

@[simp, grind =] theorem mForIn_cons (f : α → β → m (ForInStep β))
    (a : α) (as : List α) (b : β) :
    mForIn (a :: as) b f = f a b >>=ₘ
      fun | ForInStep.done b => mPure b | ForInStep.yield b => mForIn as b f :=
  mForIn'_cons (fun a' _ b => f a' b) b

section Measurability

variable [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)] [LawfulMeasurableSpaceMonad m]

@[fun_prop] theorem measurable_mForIn' (xs : List α)
    {f : (a : α) → a ∈ xs → β → m (ForInStep β)} (hf : ∀ a h, Measurable (f a h)) :
    Measurable (fun init => mForIn' xs init f) := by
  induction xs with
  | nil => exact measurable_mPure
  | cons a xs ih =>
    simp only [mForIn'_cons]
    fun_prop

@[fun_prop] theorem measurable_mForIn (xs : List α)
    {f : α → β → m (ForInStep β)} (hf : ∀ a ∈ xs, Measurable (f a)) :
    Measurable (fun init => mForIn xs init f) :=
  measurable_mForIn' xs hf

end Measurability

@[congr] theorem mForIn'_congr {as bs : List α} (w : as = bs)
    {b b' : β} (hb : b = b')
    {f : (a' : α) → a' ∈ as → β → m (ForInStep β)}
    {g : (a' : α) → a' ∈ bs → β → m (ForInStep β)}
    (h : ∀ a ha b, f a (by simpa [w] using ha) b = g a ha b) :
    mForIn' as b f = mForIn' bs b' g := by
  induction bs generalizing as b b' with
  | nil =>
    subst w
    simp [hb]
  | cons b bs ih =>
    cases as with
    | nil => simp at w
    | cons a as =>
      simp only [cons.injEq] at w
      obtain ⟨rfl, rfl⟩ := w
      simp only [mForIn'_cons]
      congr 1
      · simp [h, hb]
      · funext s
        obtain b | b := s
        · rfl
        · dsimp only
          rw [ih rfl rfl]
          intro a ha b
          exact h a (mem_cons_of_mem _ ha) b

section

variable [∀ δ, [MeasurableSpace δ] → MeasurableSpace (m δ)] [LawfulMeasurableSpaceMonad m]

theorem mForIn'_eq_mFoldlM {l : List α} (f : (a : α) → a ∈ l → β → m (ForInStep β)) (init : β)
    (hf : ∀ a h, Measurable (f a h)) :
    mForIn' l init f = ForInStep.value <$>ₘ
      l.attach.mFoldlM (fun b ⟨a, h⟩ => match b with
        | .yield b => f a h b
        | .done b => mPure (.done b)) (ForInStep.yield init) := by
  induction l generalizing init with
  | nil => simp (disch := fun_prop)
  | cons a as ih =>
    simp (disch := fun_prop) only [mForIn'_cons, attach_cons, mFoldlM_cons, mMap_mBind]
    apply MeasurableSpaceBind.bind_congr
    intro x
    match x with
    | .done b =>
      clear ih
      dsimp only
      induction as with
      | nil => simp (disch := fun_prop)
      | cons a as ih =>
        simp (disch := fun_prop) only [attach_cons, map_cons, map_map, Function.comp_def,
          mFoldlM_cons, mPure_mBind]
        specialize ih (fun a h b => f a (by
          simp only [mem_cons] at h
          rcases h with rfl | h
          · exact mem_cons_self
          · exact mem_cons_of_mem _ (mem_cons_of_mem _ h)) b) (by intros; fun_prop)
        simp [ih, mFoldlM_map]
    | .yield b =>
      simp (disch := fun_prop) [ih, mFoldlM_map]

@[simp] theorem mForIn'_yield_eq_mFoldlM {l : List α} (f : (a : α) → a ∈ l → β → m γ)
    (g : (a : α) → a ∈ l → β → γ → β) (init : β)
    (hg : ∀ a h b, Measurable (g a h b))
    (hstep : ∀ a h, Measurable (fun b => g a h b <$>ₘ f a h b)) :
    mForIn' l init (fun a h b => (fun c => .yield (g a h b c)) <$>ₘ f a h b) =
      l.attach.mFoldlM (fun b ⟨a, h⟩ => g a h b <$>ₘ f a h b) init := by
  have hbody : ∀ a h, Measurable (fun b =>
      (fun c => ForInStep.yield (g a h b c)) <$>ₘ f a h b) := by
    intro a h
    simpa (disch := fun_prop) [Function.comp_def] using
      (measurable_mMap measurable_forInStep_yield).comp (hstep a h)
  induction l generalizing init with
  | nil => simp
  | cons a as ih =>
    simp (disch := fun_prop) only [mForIn'_cons, attach_cons, mFoldlM_cons, mFoldlM_map,
      mBind_mMap_left]
    apply MeasurableSpaceBind.bind_congr
    intro c
    exact ih (fun a h => f a (mem_cons_of_mem _ h))
      (fun a h => g a (mem_cons_of_mem _ h)) _
      (fun a h b => hg a _ b) (fun a h => hstep a _) (fun a h => hbody a _)

@[simp] theorem mForIn'_pure_yield_eq_foldl {l : List α} (f : (a : α) → a ∈ l → β → β) (init : β)
    (hf : ∀ a h, Measurable (f a h)) :
    mForIn' l init (fun a h b => mPure (.yield (f a h b))) =
      mPure (f := m) (l.attach.foldl (fun b ⟨a, h⟩ => f a h b) init) := by
  induction l generalizing init with
  | nil => simp
  | cons a as ih =>
    simp (disch := fun_prop) only [mForIn'_cons, mPure_mBind]
    simp only [attach_cons, foldl_cons, foldl_map]
    exact ih (fun a h => f a (mem_cons_of_mem _ h)) (f a mem_cons_self init)
      (fun a h => hf a (mem_cons_of_mem _ h))

end

@[simp] theorem idRun_mForIn'_yield_eq_foldl
    (l : List α) (f : (a : α) → a ∈ l → β → Id β) (init : β) :
    (mForIn' (m := MId) l init
      (fun a h b => ForInStep.yield <$>ₘ f a h b)).run =
      l.attach.foldl (fun b ⟨a, h⟩ => f a h b |>.run) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih =>
    rw [mForIn'_cons]
    dsimp [mMap, mBind, mPure, bind, pure, Id.run] at *
    simp only [attach_cons, foldl_cons, foldl_map]
    exact ih (fun a h => f a (mem_cons_of_mem _ h)) (f a mem_cons_self init)

@[simp, grind =] theorem mForIn'_map {α' : Type x}
    {l : List α} (g : α → α')
    (f : (b : α') → b ∈ l.map g → β → m (ForInStep β)) {init : β} :
    mForIn' (l.map g) init f =
      mForIn' l init fun a h y => f (g a) (mem_map_of_mem h) y := by
  induction l generalizing init <;> simp_all

section

variable [∀ δ, [MeasurableSpace δ] → MeasurableSpace (m δ)] [LawfulMeasurableSpaceMonad m]

theorem mForIn_eq_mFoldlM {l : List α} (f : α → β → m (ForInStep β)) (init : β)
    (hf : ∀ a, Measurable (f a)) :
    mForIn l init f = ForInStep.value <$>ₘ
      l.mFoldlM (fun b a => match b with
        | .yield b => f a b
        | .done b => mPure (.done b)) (ForInStep.yield init) := by
  induction l generalizing init with
  | nil => simp (disch := fun_prop)
  | cons a as ih =>
    simp (disch := fun_prop) only [mFoldlM_cons, mForIn_cons, mMap_mBind]
    apply MeasurableSpaceBind.bind_congr
    intro x
    match x with
    | .done b =>
      clear ih
      dsimp only
      induction as with
      | nil => simp (disch := fun_prop)
      | cons a as ih => simp (disch := fun_prop) [ih]
    | .yield b => simp [ih]

@[simp] theorem mForIn_yield_eq_mFoldlM
    {l : List α} (f : α → β → m γ) (g : α → β → γ → β) (init : β)
    (hg : ∀ a b, Measurable (g a b))
    (hstep : ∀ a, Measurable (fun b => g a b <$>ₘ f a b)) :
    mForIn l init (fun a b => (fun c => .yield (g a b c)) <$>ₘ f a b) =
      l.mFoldlM (fun b a => g a b <$>ₘ f a b) init := by
  have hbody : ∀ a, Measurable (fun b =>
      (fun c => ForInStep.yield (g a b c)) <$>ₘ f a b) := by
    intro a
    simpa (disch := fun_prop) [Function.comp_def] using
      (measurable_mMap measurable_forInStep_yield).comp (hstep a)
  induction l generalizing init with
  | nil => simp
  | cons a as ih =>
    simp (disch := fun_prop) only [mForIn_cons, mFoldlM_cons, mBind_mMap_left]
    apply MeasurableSpaceBind.bind_congr
    intro c
    exact ih _

@[simp] theorem mForIn_pure_yield_eq_foldl {l : List α} (f : α → β → β) (init : β)
    (hf : ∀ a, Measurable (f a)) :
    mForIn l init (fun a b => mPure (.yield (f a b))) =
      mPure (f := m) (l.foldl (fun b a => f a b) init) := by
  induction l generalizing init with
  | nil => simp
  | cons a as ih =>
    simp (disch := fun_prop) only [mForIn_cons, mPure_mBind]
    exact ih _

end

@[simp] theorem idRun_mForIn_yield_eq_foldl
    (l : List α) (f : α → β → Id β) (init : β) :
    (mForIn (m := MId) l init
      (fun a b => ForInStep.yield <$>ₘ f a b)).run =
      l.foldl (fun b a => f a b |>.run) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih =>
    rw [mForIn_cons]
    dsimp [mMap, mBind, mPure, bind, pure, Id.run] at *
    exact ih (f a init)

@[simp, grind =] theorem mForIn_map {α' : Type x}
    {l : List α} {g : α → α'} {f : α' → β → m (ForInStep β)} {init : β} :
    mForIn (l.map g) init f = mForIn l init fun a y => f (g a) y := by
  induction l generalizing init <;> simp_all

end List

namespace MeasureTheory.Internal

open Std.Internal

universe u u₁ v w

/-- Containers whose `MeasurableSpaceForIn` loop produces its elements without effects in `m`.
Analogous to core Lean's `Std.Internal.PureForIn`. -/
class PureMeasurableSpaceForIn (m : (α : Type u) → [MeasurableSpace α] → Type v)
    (ρ : Type w) (α : Type u₁) [MeasurableSpaceMonad m]
    [MeasurableSpaceForIn m ρ α] [ForIn Id ρ α] : Prop where
  /-- Iterating over `xs` is equivalent to iterating over `ForIn.toList xs`. -/
  mForIn_eq {β : Type u} [MeasurableSpace β] (xs : ρ) (init : β)
      (f : α → β → m (ForInStep β)) :
    mForIn xs init f = mForIn (ForIn.toList xs) init f

/-- Containers whose `MeasurableSpaceForIn'` loop produces its elements without effects in `m`,
carrying a membership proof for each. Analogous to core Lean's `Std.Internal.PureForIn'`. -/
class PureMeasurableSpaceForIn' (m : (α : Type u) → [MeasurableSpace α] → Type v)
    (ρ : Type w) (α : Type u₁) [MeasurableSpaceMonad m]
    {d : Membership α ρ} [MeasurableSpaceForIn' m ρ α d] [ForIn Id ρ α]
    [LawfulMemForInId ρ α] : Prop where
  /-- Iterating over `xs` is equivalent to iterating over `ForIn.toList xs`. -/
  mForIn'_eq {β : Type u} [MeasurableSpace β] (xs : ρ) (init : β)
      (f : (a : α) → a ∈ xs → β → m (ForInStep β)) :
    mForIn' xs init f = mForIn' (ForIn.toList xs) init fun a h b =>
      f a (LawfulMemForInId.mem_toList_iff.mp h) b

private theorem mForIn'_cast {γ : Type u₁} {δ : Type u}
    {n : (α : Type u) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad n]
    [MeasurableSpace δ] {l l' : List γ} (hl : l = l') (init : δ)
    (f : (a : γ) → a ∈ l' → δ → n (ForInStep δ)) :
    mForIn' l init (fun a ha b => f a (hl ▸ ha) b) = mForIn' l' init f :=
  List.mForIn'_congr hl rfl fun _ _ _ => rfl

variable {m : (α : Type u) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
  {α : Type u₁}

instance : PureMeasurableSpaceForIn' m (List α) α where
  mForIn'_eq xs init f := (mForIn'_cast (ForIn.toList_list xs) init f).symm

instance : PureMeasurableSpaceForIn m (List α) α where
  mForIn_eq xs init f := by rw [ForIn.toList_list]

end MeasureTheory.Internal
