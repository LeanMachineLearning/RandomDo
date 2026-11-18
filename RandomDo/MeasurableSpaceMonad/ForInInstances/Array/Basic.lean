/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.MeasurableSpaceMonad.ForInInstances.List

/-!
# Array and vector iteration for measurable space monads

This file defines the `MeasurableSpaceForIn'` instances for `Array`s and `Vector`s in `rdo`
notation, together with lemmas relating array iteration to list iteration. The vector instance
uses the array implementation.

The implementation follows `Array.forIn'` in `Init/Data/Array/Basic.lean`, and the correspondence
lemmas follow `Init/Data/List/ToArray.lean`.
-/

@[expose] public section

namespace MeasureTheory

universe uρ uα u v w

section Collections

variable {α : Type uα} {m : (α : Type u) → [MeasurableSpace α] → Type v}
  [MeasurableSpaceMonad m] {β : Type u} [MeasurableSpace β]

section Array

open _root_.Array

/-- Compiler implementation of `Array.mForIn'` using `USize` indices.
Analogue of core's `Array.forIn'Unsafe`. As in core, this relies on the runtime bound on array
sizes to represent each valid index by a `USize`. -/
@[inline] unsafe def Array.mForIn'Unsafe
    (as : Array α) (b : β) (f : (a : α) → a ∈ as → β → m (ForInStep β)) : m β :=
  let sz := as.usize
  let rec @[specialize, nolint docBlame] loop (i : USize) (b : β) : m β := rdo
    if i < sz then
      let a := as.uget i lcProof
      match (← f a lcProof b) with
      | ForInStep.done  b => mPure b
      | ForInStep.yield b => loop (i+1) b
    else
      mPure b
  loop 0 b

/-- Reference implementation of iteration over an array, with a membership proof.
Analogue of core's `Array.forIn'`. -/
@[implemented_by Array.mForIn'Unsafe]
protected def Array.mForIn'
    (as : Array α) (b : β) (f : (a : α) → a ∈ as → β → m (ForInStep β)) : m β :=
  let rec @[nolint docBlame] loop (i : Nat) (h : i ≤ as.size) (b : β) : m β := rdo
    match i, h with
    | 0,   _ => mPure b
    | i+1, h =>
      have h' : i < as.size            := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) h
      have : as.size - 1 < as.size     := Nat.sub_lt (Nat.zero_lt_of_lt h') (by decide)
      have : as.size - 1 - i < as.size := Nat.lt_of_le_of_lt (Nat.sub_le (as.size - 1) i) this
      match (← f as[as.size - 1 - i] (getElem_mem this) b) with
      | ForInStep.done b  => mPure b
      | ForInStep.yield b => loop i (Nat.le_of_lt h') b
  loop as.size (Nat.le_refl _) b

instance : MeasurableSpaceForIn' m (Array α) α inferInstance where
  mForIn' := Array.mForIn'

@[simp] theorem Array.mForIn'_eq_mForIn' :
    Array.mForIn' (m := m) (α := α) (β := β) = mForIn' := rfl

instance {n : ℕ} : MeasurableSpaceForIn' m (Vector α n) α inferInstance where
  mForIn' xs b f := Array.mForIn' xs.toArray b (fun a h b => f a (by simpa using h) b)

end Array

end Collections

end MeasureTheory

/-! ## Array-to-list correspondence -/

open MeasureTheory

namespace List

universe u v w

variable {α : Type u} {β : Type v} [MeasurableSpace β]
  {m : (γ : Type v) → [MeasurableSpace γ] → Type w} [MeasurableSpaceMonad m]

#check _root_.List.forIn'_loop_toArray

@[simp] theorem mForIn'_loop_toArray (l : List α)
    (f : (a : α) → a ∈ l.toArray → β → m (ForInStep β)) (i : Nat)
    (h : i ≤ l.length) (b : β) :
    MeasureTheory.Array.mForIn'.loop l.toArray f i h b =
      mForIn' (l.drop (l.length - i)) b
        (fun a ha b => f a (by simpa using mem_of_mem_drop ha) b) := by
  induction i generalizing l b with
  | zero => simp [MeasureTheory.Array.mForIn'.loop]
  | succ i ih =>
    simp only [MeasureTheory.Array.mForIn'.loop, size_toArray,
      getElem_toArray, ih]
    have t : l.drop (l.length - (i + 1)) =
        l[l.length - i - 1] :: l.drop (l.length - i) := by
      simp only [Nat.sub_add_eq]
      rw [drop_sub_one (by omega), getElem?_eq_getElem (by omega)]
      simp
    simp only [t, mForIn'_cons, Nat.sub_sub, Nat.add_comm]
    congr

#check _root_.List.forIn'_toArray

@[simp, grind =] theorem mForIn'_toArray (l : List α) (b : β)
    (f : (a : α) → a ∈ l.toArray → β → m (ForInStep β)) :
    mForIn' l.toArray b f =
      mForIn' l b (fun a ha b => f a (mem_toArray.mpr ha) b) := by
  rw [← MeasureTheory.Array.mForIn'_eq_mForIn',
    MeasureTheory.Array.mForIn', mForIn'_loop_toArray]
  simp

#check _root_.List.forIn_toArray

@[simp, grind =] theorem mForIn_toArray (l : List α) (b : β) (f : α → β → m (ForInStep β)) :
    mForIn l.toArray b f = mForIn l b f :=
  mForIn'_toArray l b (fun a _ b => f a b)

end List
