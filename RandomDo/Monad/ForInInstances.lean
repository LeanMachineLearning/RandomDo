/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.Monad.Notation

/-!
# Instances for `MeasurableSpaceForIn`

**TODO**

-/

@[expose] public section

section MeasurableSpace

variable {α : Type*} [MeasurableSpace α]

instance : MeasurableSpace (List α) :=
  MeasurableSpace.comap List.equivSigmaTuple inferInstance

instance : MeasurableSpace (Array α) :=
  MeasurableSpace.comap Array.toList inferInstance

instance {n : ℕ} : MeasurableSpace (Vector α n) :=
  MeasurableSpace.comap Vector.toArray inferInstance

instance instMeasurableSpaceSubarray : MeasurableSpace (Subarray α) :=
  MeasurableSpace.comap (fun s : Subarray α ↦ s.toList) inferInstance

@[fun_prop]
lemma measurable_toList : Measurable (Array.toList : Array α → List α) :=
  Measurable.of_comap_le fun _ a ↦ a

@[fun_prop]
lemma measurable_subarray_toList : Measurable (fun s : Subarray α ↦ s.toList) :=
  Measurable.of_comap_le fun _ a ↦ a

@[fun_prop]
lemma measurable_toArray {n : ℕ} : Measurable (Vector.toArray : Vector α n → Array α) :=
  Measurable.of_comap_le fun _ a ↦ a

end MeasurableSpace

universe u v

open MeasurableSpacePure

variable {α : Type u} [mα : MeasurableSpace α] {m : (α : Type u) → [MeasurableSpace α] → Type v}

section Array

/-- Compiler implementation for `forIn` -/
@[inline] unsafe def Array.measurableSpaceForIn'Unsafe [MeasurableSpaceMonad m]
  {β : Type u} [mβ : MeasurableSpace β]
  (as : Array α) (b : β) (f : (a : α) → a ∈ as → β → m (ForInStep β)) : m β :=
  let sz := as.usize
  let rec @[specialize] loop (i : USize) (b : β) : m β := rdo
    if i < sz then
      let a := as.uget i lcProof
      match (← f a lcProof b) with
      | ForInStep.done  b => mPure b
      | ForInStep.yield b => loop (i+1) b
    else
      mPure b
  loop 0 b

/-- Reference implementation for `forIn'` -/
@[implemented_by Array.measurableSpaceForIn'Unsafe]
protected def Array.measurableSpaceForIn' [MeasurableSpaceMonad m]
  {β : Type u} [mβ : MeasurableSpace β]
  (as : Array α) (b : β) (f : (a : α) → a ∈ as → β → m (ForInStep β)) : m β :=
  let rec loop (i : Nat) (h : i ≤ as.size) (b : β) : m β := rdo
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

instance [MeasurableSpaceMonad m] : MeasurableSpaceForIn' m (Array α) α inferInstance where
  forIn' := Array.measurableSpaceForIn'

instance {n : ℕ} [MeasurableSpaceMonad m] :
    MeasurableSpaceForIn' m (Vector α n) α inferInstance where
  forIn' xs b f := Array.measurableSpaceForIn' xs.toArray b (fun a h b => f a (by simpa using h) b)

end Array

section List

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [Ring α]

/-- implementation for `forIn'` -/
@[inline]
protected def List.measurableSpaceForIn' [MeasurableSpaceMonad m]
    {β : Type u} [mβ : MeasurableSpace β] (as : @& List α) (init : β)
    (f : (a : α) → a ∈ as → β → m (ForInStep β)) : m β :=
  let rec @[specialize]
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

@[simps]
instance [MeasurableSpaceMonad m] : MeasurableSpaceForIn' m (List α) α inferInstance where
  forIn' := List.measurableSpaceForIn'

end List
