/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.ForMathlib.MeasureTheory.MeasurableSpace.Collections
public import RandomDo.MeasurableSpaceMonad.ForIn
public import RandomDo.Monad.Notation
public import RandomDo.MeasurableSpaceMonad.ForInInstances.Ranges

/-!
# Collection and iterator instances for measurable space monads

This file provides `MeasurableSpaceForIn'` instances for `List`, `Array`, and `Vector` in any
`MeasurableSpaceMonad`, and `MeasurableSpaceForIn` instances for `Std.Iter` and `Std.IterM`,
including their `Total` and `Partial` wrappers. Together with `RandomDo.Monad.Notation`, these
instances support `for x in xs rdo ...`. The range instances additionally support direct range
syntax such as `for i in 0...n rdo ...`, including membership proofs.
The membership-aware instances additionally support
`for h : x in xs rdo ...`.

Each consumer threads the loop state through the body. `ForInStep.yield` continues iteration
and `ForInStep.done` stops immediately. Only the loop state needs a `MeasurableSpace` instance;
the elements, collection, and internal iterator state do not. Lists, arrays, vectors, and pure
iterators allow the element universe to differ from the loop-state universe.

## Main definitions

* `List.measurableSpaceForIn'`, `Array.measurableSpaceForIn'`: iteration with a membership proof.
  The vector instance delegates to the array implementation through `Vector.toArray`.
* `Iter.instMeasurableSpaceForIn'`, `IterM.instMeasurableSpaceForIn'`: opt-in membership-aware
  consumers for iterators. As in core, the generic membership relation is an internal predicate,
  so these definitions and their `Total`/`Partial` variants are not global instances.
* `Iter.forIn_eq_match_step`: unfolds a finite pure iterator loop by one step.

## Implementation details

The list, array, and vector implementations follow Lean core's `List.forIn'`, `Array.forIn'`,
and vector `ForIn'` instance in `Init/Data/List/Control.lean`, `Init/Data/Array/Basic.lean`, and
`Init/Data/Vector/Basic.lean`. They replace `Monad`, `do`, and `pure` with
`MeasurableSpaceMonad`, `rdo`, and `mPure`, and take a measurable space on the loop state.
As in core, lists use borrowing and a specialized recursive loop. Arrays have a structurally
recursive reference definition and a compiler implementation using `USize` indices, connected
by `implemented_by`.

Iterator consumers are defined in `ForInInstances.Iterators` and `ForInInstances.Ranges`.
They adapt core's generic and specialized range loops to use measurable bind directly. The same
consumer serves `Measure` and adapted ordinary monads; producer effects and loop-body effects remain
interleaved. The `Total` wrappers retain core's `Finite` requirement. Ordinary consumers can also
traverse potentially infinite iterators.

-/

@[expose] public section

namespace MeasureTheory

universe uρ uα u v w

open MeasurableSpacePure MeasurableSpaceBind

section Collections

variable {α : Type uα} {m : (α : Type u) → [MeasurableSpace α] → Type v}
  [MeasurableSpaceMonad m] {β : Type u} [MeasurableSpace β]

section Array

open _root_.Array

/-- Compiler implementation of `Array.measurableSpaceForIn'` using `USize` indices.
Analogue of core's `Array.forIn'Unsafe`. As in core, this relies on the runtime bound on array
sizes to represent each valid index by a `USize`. -/
@[inline] unsafe def Array.measurableSpaceForIn'Unsafe
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
@[implemented_by Array.measurableSpaceForIn'Unsafe]
protected def Array.measurableSpaceForIn'
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
  forIn' := Array.measurableSpaceForIn'

@[simp] theorem Array.measurableSpaceForIn'_eq_forIn' :
    Array.measurableSpaceForIn' (m := m) (α := α) (β := β) = forIn' := rfl

instance {n : ℕ} : MeasurableSpaceForIn' m (Vector α n) α inferInstance where
  forIn' xs b f := Array.measurableSpaceForIn' xs.toArray b (fun a h b => f a (by simpa using h) b)

end Array

section List

open _root_.List

/-- Iteration over a list, with a membership proof. Analogue of core's `List.forIn'`. -/
@[inline]
protected def List.measurableSpaceForIn' (as : @& List α) (init : β)
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
  forIn' := List.measurableSpaceForIn'

@[simp, grind =] theorem List.measurableSpaceForIn'_eq_forIn' :
    List.measurableSpaceForIn' (m := m) (α := α) (β := β) = forIn' := rfl

end List

end Collections

end MeasureTheory
