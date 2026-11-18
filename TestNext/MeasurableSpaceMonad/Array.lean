/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

import all RandomDo.MeasurableSpaceMonad.Array
import RandomDo.MeasurableSpaceMonad.Instances.Measure
import RandomDo.MeasurableSpaceMonad.Instances.PseudoRandom
meta import RandomDo.MeasurableSpaceMonad.Array
meta import RandomDo.MeasurableSpaceMonad.Instances.PseudoRandom

/-!
# Measurable space monadic array regression checks

The state records the order of effects. These checks cover the in-place mapping workers,
bounded folds, early exit, and truncation at the shorter input. The kernel checks exercise the
safe reference definitions; `#guard` exercises the compiler implementations. A polymorphic
mapper is also interpreted in `Measure`.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

open MeasureTheory

namespace TestNext.MeasurableSpaceMonad.Array

private def record (n : Nat) : PseudoRand Nat Nat :=
  fun s => (n, ⟨10 * s.down + n⟩)

private def run {α : Type} [MeasurableSpace α] (action : PseudoRand Nat α) : α × Nat :=
  let (a, s) := action ⟨0⟩
  (a, s.down)

private def collect {m : (α : Type) → [MeasurableSpace α] → Type} [MeasurableSpaceMonad m]
    (sample : Nat → m Nat) (xs : Array Nat) : m (Array Nat) :=
  xs.mMapM sample

-- Mapping must preserve the input's value when it is shared, and preserve action order.
#guard (let xs := #[1, 3, 7]; (xs, run (collect record xs))) ==
  (#[1, 3, 7], (#[1, 3, 7], 137))
#guard run (#[1, 3, 7].mMapM (fun a => rdo return (← record a) == 3)) ==
  (#[false, true, false], 137)
#guard run (#[1, 3, 7].mMapIdxM (fun i a => rdo return (i, ← record a))) ==
  (#[(0, 1), (1, 3), (2, 7)], 137)
#guard run (#[1, 3, 7].mMapFinIdxM (fun i a h => rdo
  let a ← record a
  return (i, a, #[1, 3, 7][i]))) == (#[(0, 1, 1), (1, 3, 3), (2, 7, 7)], 137)

-- Bounded folds clamp to the input size, and empty intervals perform no actions.
private def left (xs : Array Nat) (start stop : Nat) : PseudoRand Nat Nat :=
  xs.mFoldlM (fun acc a => rdo return acc + (← record a)) 0 start stop

private def right (xs : Array Nat) (start stop : Nat) : PseudoRand Nat Nat :=
  xs.mFoldrM (fun a acc => rdo return acc + (← record a)) 0 start stop

#guard run (left #[1, 3, 7] 1 100) == (10, 37)
#guard run (right #[1, 3, 7] 100 1) == (10, 73)
#guard run (left #[1, 3, 7] 4 100) == (0, 0)
#guard run (right #[1, 3, 7] 1 2) == (0, 0)

-- Filtering preserves output order even when predicates are evaluated right to left.
private def keep (a : Nat) : PseudoRand Nat Bool := rdo
  return (← record a) != 3

#guard run (#[1, 3, 7].mFilterM keep) == (#[1, 7], 137)
#guard run (#[1, 3, 7].mFilterRevM keep) == (#[1, 7], 731)
#guard run (#[1, 3, 7].mFilterMapM (fun a => rdo
  return if (← keep a) then some (2 * a) else none)) == (#[2, 14], 137)
#guard run (#[1, 3, 7].mFlatMapM (fun a => rdo
  let a ← record a
  return if a = 3 then #[] else #[a, a])) == (#[1, 1, 7, 7], 137)

-- Zipping stops at either shorter input, without performing unmatched actions.
private def pair (a b : Nat) : PseudoRand Nat (Nat × Nat) := rdo
  return (← record a, ← record b)

#guard run (Array.mZipWithM pair #[1, 3, 7] #[2, 4]) == (#[(1, 2), (3, 4)], 1234)
#guard run (Array.mZipWithM pair #[1, 3] #[2, 4, 8]) == (#[(1, 2), (3, 4)], 1234)

-- The predicate/search family must stop as soon as the answer is known.
private def isThree (a : Nat) : PseudoRand Nat Bool := rdo
  return (← record a) == 3

#guard run (#[1, 3, 7].mAnyM isThree) == (true, 13)
#guard run (#[1, 3, 7].mAllM keep) == (false, 13)
#guard run (#[1, 3, 7].mAnyM isThree 2 100) == (false, 7)
#guard run (#[1, 3, 7].mAnyM isThree 4 100) == (false, 0)
#guard run (#[1, 3, 7].mFindM? isThree) == (some 3, 13)
#guard run (#[1, 3, 7].mFindRevM? isThree) == (some 3, 73)
#guard run (#[1, 3, 7].mFindIdxM? isThree) == (some 1, 13)
#guard run (#[1, 7].mFindIdxM? isThree) == (none, 17)
#guard run (#[1, 3, 7].mFindSomeM? (fun a => rdo
  return if (← isThree a) then some (a + 1) else none)) == (some 4, 13)

-- Kernel reduction checks the reference implementations, independently of `implemented_by`.
example : Id.run (#[1, 3, 7].mMapIdxM (m := MId)
    (fun i a => mPure (i + a))) = #[1, 4, 9] := by decide
example : Id.run (#[1, 3, 7].mFoldlM (m := MId)
    (fun acc a => mPure (10 * acc + a)) (0 : Nat) 1 100) = 37 := by decide
example : Id.run (#[1, 3, 7].mFoldrM (m := MId)
    (fun a acc => mPure (10 * acc + a)) (0 : Nat) 100 1) = 73 := by decide

-- The same polymorphic definition must preserve measure effects, including zero.
example : collect (m := Measure) (fun _ => 0) #[1, 3, 7] = 0 := by
  rw [collect, Array.mMapM_eq_mMapM_toList]
  · simp [List.mMapM, List.mMapM.loop, mMap, mBind]
  · intro a
    simp [mMap]

end TestNext.MeasurableSpaceMonad.Array
