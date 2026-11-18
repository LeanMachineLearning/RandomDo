/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

import all RandomDo.MeasurableSpaceMonad.List
import RandomDo.MeasurableSpaceMonad.Instances.Measure
import RandomDo.MeasurableSpaceMonad.Instances.PseudoRandom
import Mathlib.MeasureTheory.Measure.Prod
meta import RandomDo.MeasurableSpaceMonad.List
meta import RandomDo.MeasurableSpaceMonad.Instances.PseudoRandom

/-!
# Monadic list regression checks

The sampler state records execution order, including actions that must be skipped by zip and
search. The same polymorphic map also runs in `Measure`. The final check proves that the
additional callback hypothesis is usable for arbitrary s-finite measures, without assuming a
countable output type or a stronger measurable monad class.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

open MeasureTheory

namespace TestNext.MeasurableSpaceMonad.List

private def record (n : Nat) : PseudoRand Nat Nat :=
  fun s => (n, ⟨10 * s.down + n⟩)

private def run {α : Type} [MeasurableSpace α] (action : PseudoRand Nat α) : α × Nat :=
  let (a, s) := action ⟨0⟩
  (a, s.down)

private def collect {m : (α : Type) → [MeasurableSpace α] → Type} [MeasurableSpaceMonad m]
    (sample : Nat → m Nat) (xs : List Nat) : m (List Nat) :=
  xs.mMapM sample

-- Tail-recursive accumulation must preserve both output order and action order.
#guard run (collect record [1, 3, 7]) == ([1, 3, 7], 137)

-- Reaching the shorter list must stop before the unmatched element's action runs.
#guard run (List.mZipWithM
    (fun a b => rdo let _ ← record a; record b) [1, 3, 7] [2, 4]) == ([2, 4], 1234)

-- Finding a result must skip later effects; `none` must continue the search.
#guard run (List.mFindSomeM?
    (fun a => rdo
      let a ← record a
      return if a = 3 then some a else none) [1, 3, 7]) == (some 3, 13)

-- The polymorphic implementation must preserve measure effects, including annihilation by zero.
example : collect (m := Measure) (fun _ => 0) [1, 3, 7] = 0 := by
  simp [collect, List.mMapM, List.mMapM.loop, mBind]

-- S-finiteness of each sampled measure suffices for the captured list-accumulator callback.
example {α β : Type} [MeasurableSpace β]
    (f : α → Measure β) [∀ a, SFinite (f a)] (a : α) (as : List α) :
    List.mMapM f (a :: as) =
      (rdo return (← f a) :: (← List.mMapM f as)) := by
  apply List.mMapM_cons
  intro a
  have h : Measurable (fun bs : List β =>
      ((f a).map (fun b => (b, bs))).map (fun p => p.1 :: p.2)) :=
    (Measure.measurable_map _ measurable_list_cons).comp Measurable.map_prodMk_right
  simpa (disch := fun_prop)
    [mMap, Function.comp_def, Measure.bind_dirac_eq_map, Measure.map_map] using h

end TestNext.MeasurableSpaceMonad.List
