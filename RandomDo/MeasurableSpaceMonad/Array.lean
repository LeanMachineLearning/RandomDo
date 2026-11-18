/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.MeasurableSpaceMonad.List
public import RandomDo.ForMathlib.MeasureTheory.MeasurableSpace.Array
public import RandomDo.MeasurableSpaceMonad.ForInInstances.Array.Basic
public import RandomDo.RDo.Loop

/-!
# Measurable space monadic array operations

This file defines monadic array operations for measurable space monads, including mapping,
filtering, folding, and searching, together with their laws, measurability lemmas, and
array-to-list correspondence lemmas.

## Main definitions

* `mMapM`: map a measurable space monadic function over an array.
* `mFilterM`: filter an array using a measurable space monadic predicate.
* `mFoldlM` and `mFoldrM`: fold a measurable space monadic function from left to right or right
  to left.
-/

@[expose] public section

open MeasureTheory

namespace Array

universe u v w x

/-! ## Executable operations -/

/-- Compiler implementation of `Array.mFoldlM`. Analogue of core's `Array.foldlMUnsafe`. -/
@[inline]
unsafe def mFoldlMUnsafe {α : Type u} {β : Type v}
    {m : (α : Type v) → [MeasurableSpace α] → Type w} [MeasurableSpaceMonad m] [MeasurableSpace β]
    (f : β → α → m β) (init : β) (as : Array α) (start := 0) (stop := as.size) : m β :=
  let rec @[specialize, nolint docBlame] fold (i : USize) (stop : USize) (b : β) : m β := rdo
    if i == stop then
      mPure b
    else
      fold (i+1) stop (← f b (as.uget i lcProof))
  if start < stop then
    if stop ≤ as.size then
      fold (USize.ofNat start) (USize.ofNat stop) init
    else if start < as.size then
      fold (USize.ofNat start) (USize.ofNat as.size) init
    else
      mPure init
  else
    mPure init

/-- Folds a measurable space monadic function over an array from the left, accumulating a value
starting with `init`. The accumulated value is combined with each element of the array in order,
using `f`. Analogue of core's `Array.foldlM`.

The optional parameters `start` and `stop` control the region of the array to be folded. Folding
proceeds from `start` (inclusive) to `stop` (exclusive), so no folding occurs unless `start < stop`.
By default, the entire array is folded. -/
@[implemented_by mFoldlMUnsafe]
def mFoldlM {α : Type u} {β : Type v} {m : (α : Type v) → [MeasurableSpace α] → Type w}
    [MeasurableSpaceMonad m] [MeasurableSpace β] (f : β → α → m β) (init : β) (as : Array α)
    (start := 0) (stop := as.size) : m β :=
  let fold (stop : Nat) (h : stop ≤ as.size) :=
    let rec loop (i : Nat) (j : Nat) (b : β) : m β := rdo
      if hlt : j < stop then
        match i with
        | 0    => mPure b
        | i'+1 =>
          have : j < as.size := Nat.lt_of_lt_of_le hlt h
          loop i' (j+1) (← f b as[j])
      else
        mPure b
    loop (stop - start) start init
  if h : stop ≤ as.size then
    fold stop h
  else
    fold as.size (Nat.le_refl _)


/-- Compiler implementation of `Array.mFoldrM`. Analogue of core's `Array.foldrMUnsafe`. -/
@[inline]
unsafe def mFoldrMUnsafe {α : Type u} {β : Type v}
    {m : (α : Type v) → [MeasurableSpace α] → Type w} [MeasurableSpaceMonad m] [MeasurableSpace β]
    (f : α → β → m β) (init : β) (as : Array α) (start := as.size) (stop := 0) : m β :=
  let rec @[specialize, nolint docBlame] fold (i : USize) (stop : USize) (b : β) : m β := rdo
    if i == stop then
      mPure b
    else
      fold (i-1) stop (← f (as.uget (i-1) lcProof) b)
  if start ≤ as.size then
    if stop < start then
      fold (USize.ofNat start) (USize.ofNat stop) init
    else
      mPure init
  else if stop < as.size then
    fold (USize.ofNat as.size) (USize.ofNat stop) init
  else
    mPure init

/-- Folds a measurable space monadic function over an array from the right, accumulating a value
starting with `init`. The accumulated value is combined with each element of the array in reverse
order, using `f`. Analogue of core's `Array.foldrM`.

The optional parameters `start` and `stop` control the region of the array to be folded. Folding
proceeds from `start` (exclusive) to `stop` (inclusive), so no folding occurs unless `start > stop`.
By default, the entire array is folded. -/
@[implemented_by mFoldrMUnsafe]
def mFoldrM {α : Type u} {β : Type v} {m : (α : Type v) → [MeasurableSpace α] → Type w}
    [MeasurableSpaceMonad m] [MeasurableSpace β] (f : α → β → m β) (init : β) (as : Array α)
    (start := as.size) (stop := 0) : m β :=
  let rec fold (i : Nat) (h : i ≤ as.size) (b : β) : m β := rdo
    if i == stop then
      mPure b
    else match i, h with
      | 0, _   => mPure b
      | i+1, h =>
        have : i < as.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h
        fold i (Nat.le_of_lt this) (← f as[i] b)
  if h : start ≤ as.size then
    if stop < start then
      fold start h init
    else
      mPure init
  else if stop < as.size then
    fold as.size (Nat.le_refl _) init
  else
    mPure init

/-- Compiler implementation of `mMapM`. Analogue of core's `Array.mapMUnsafe`. -/
@[inline]
unsafe def mMapMUnsafe {α : Type u} {β : Type v} {m : (α : Type v) → [MeasurableSpace α] → Type w}
    [MeasurableSpaceMonad m] [MeasurableSpace β] (f : α → m β) (as : Array α) : m (Array β) :=
  -- Carry β's measurable space through the same type erasure as core's worker.
  letI : MeasurableSpace PNonScalar.{v} := unsafeCast (inferInstance : MeasurableSpace β)
  let sz := as.usize
  let rec @[specialize, nolint docBlame] map (i : USize) (bs : Array NonScalar) :
      m (Array PNonScalar.{v}) := rdo
    if i < sz then
     let v    := bs.uget i lcProof
     -- Replace bs[i] by `box(0)`.  This ensures that `v` remains unshared if possible.
     -- Note: we assume that arrays have a uniform representation irrespective
     -- of the element type, and that it is valid to store `box(0)` in any array.
     let bs'    := bs.uset i default lcProof
     let vNew ← f (unsafeCast v)
     map (i+1) (bs'.uset i (unsafeCast vNew) lcProof)
    else
     mPure (unsafeCast bs)
  unsafeCast <| map 0 (unsafeCast as)

/-- Applies the measurable space monadic action `f` to every element in the array, left-to-right,
and returns the array of results. Analogue of core's `Array.mapM`. -/
@[implemented_by mMapMUnsafe]
def mMapM {α : Type u} {β : Type v} {m : (α : Type v) → [MeasurableSpace α] → Type w}
    [MeasurableSpaceMonad m] [MeasurableSpace β] (f : α → m β) (as : Array α) : m (Array β) :=
  -- Note: we cannot use `mFoldlM` here for the reference implementation because this calls
  -- `mBind` and `mPure` too many times. (We do not assume `LawfulMeasurableSpaceMonad m`.)
  let rec map (i : Nat) (bs : Array β) : m (Array β) := rdo
      if hlt : i < as.size then
        map (i+1) (bs.push (← f as[i]))
      else
        mPure bs
  decreasing_by decreasing_trivial_pre_omega
  map 0 (emptyWithCapacity as.size)

/-- Compiler implementation of `mMapFinIdxM`. Analogue of core's `Array.mapFinIdxMUnsafe`. -/
@[inline]
unsafe def mMapFinIdxMUnsafe {α : Type u} {β : Type v}
    {m : (α : Type v) → [MeasurableSpace α] → Type w} [MeasurableSpaceMonad m] [MeasurableSpace β]
    (as : Array α) (f : (i : Nat) → α → (h : i < as.size) → m β) : m (Array β) :=
  -- Carry β's measurable space through the same type erasure as core's worker.
  letI : MeasurableSpace PNonScalar.{v} := unsafeCast (inferInstance : MeasurableSpace β)
  let sz := as.usize
  let rec @[specialize, nolint docBlame] map (i : USize) (bs : Array NonScalar) :
      m (Array PNonScalar.{v}) := rdo
    if i < sz then
     let v    := bs.uget i lcProof
     -- Replace bs[i] by `box(0)`.  This ensures that `v` remains unshared if possible.
     -- Note: we assume that arrays have a uniform representation irrespective
     -- of the element type, and that it is valid to store `box(0)` in any array.
     let bs'    := bs.uset i default lcProof
     let vNew ← f i.toNat (unsafeCast v) lcProof
     map (i+1) (bs'.uset i (unsafeCast vNew) lcProof)
    else
     mPure (unsafeCast bs)
  unsafeCast <| map 0 (unsafeCast as)

/-- Applies the measurable space monadic action `f` to every element in the array, along with the
element's index and a proof that the index is in bounds, from left to right. Returns the array of
results. Analogue of core's `Array.mapFinIdxM`. -/
@[implemented_by mMapFinIdxMUnsafe]
def mMapFinIdxM {α : Type u} {β : Type v} {m : (α : Type v) → [MeasurableSpace α] → Type w}
    [MeasurableSpaceMonad m] [MeasurableSpace β]
    (as : Array α) (f : (i : Nat) → α → (h : i < as.size) → m β) : m (Array β) :=
  let rec @[specialize, nolint docBlame] map (i : Nat) (j : Nat) (inv : i + j = as.size)
      (bs : Array β) : m (Array β) := rdo
    match i, inv with
    | 0,    _  => mPure bs
    | i+1, inv =>
      have j_lt : j < as.size := by
        rw [← inv, Nat.add_assoc, Nat.add_comm 1 j, Nat.add_comm]
        apply Nat.le_add_right
      have : i + (j + 1) = as.size := by rw [← inv, Nat.add_comm j 1, Nat.add_assoc]
      map i (j+1) this (bs.push (← f j as[j] j_lt))
  map as.size 0 rfl (emptyWithCapacity as.size)

/-- Applies the measurable space monadic action `f` to every element in the array, along with the
element's index, from left to right. Returns the array of results.
Analogue of core's `Array.mapIdxM`. -/
@[inline]
def mMapIdxM {α : Type u} {β : Type v} {m : (α : Type v) → [MeasurableSpace α] → Type w}
    [MeasurableSpaceMonad m] [MeasurableSpace β] (f : Nat → α → m β) (as : Array α) : m (Array β) :=
  as.mMapFinIdxM fun i a _ => f i a

/-- Returns the first non-`none` result of applying the measurable space monadic function `f` to
each element of the array, in order. Returns `none` if `f` returns `none` for all elements. Analogue
of core's `Array.findSomeM?`. -/
@[inline]
def mFindSomeM? {α : Type u} {β : Type v} {m : (α : Type v) → [MeasurableSpace α] → Type w}
    [MeasurableSpaceMonad m] [MeasurableSpace β] (f : α → m (Option β)) (as : Array α) : m
    (Option β) := rdo
  for a in as rdo
    match (← f a) with
    | some b => return some b
    | _      => mPure ⟨⟩
  return none

/-- Returns the first element of the array for which the measurable space monadic predicate `p`
returns `true`, or `none` if no such element is found. Elements of the array are checked in order.
Analogue of core's `Array.findM?`.

The measurable space monad `m` takes value types in `Type` to avoid needing to use `ULift Bool` in
`p`'s type. -/
@[inline]
def mFindM? {α : Type} [MeasurableSpace α] {m : (γ : Type) → [MeasurableSpace γ] → Type w}
    [MeasurableSpaceMonad m] (p : α → m Bool) (as : Array α) : m (Option α) := rdo
  for a in as rdo
    if (← p a) then
      return some a
  return none

/-- Finds the index of the first element of an array for which the measurable space monadic
predicate `p` returns `true`. Elements are examined in order from left to right, and the search is
terminated when an element that satisfies `p` is found. If no such element exists in the array, then
`none` is returned. Analogue of core's `Array.findIdxM?`. -/
@[inline]
def mFindIdxM? {α : Type u} {m : (γ : Type) → [MeasurableSpace γ] → Type w}
    [MeasurableSpaceMonad m] (p : α → m Bool) (as : Array α) : m (Option Nat) := rdo
  let mut i := 0
  for a in as rdo
    if (← p a) then
      return some i
    i := i + 1
  return none

/-- Compiler implementation of `mAnyM`. Analogue of core's `Array.anyMUnsafe`. -/
@[inline]
unsafe def mAnyMUnsafe {α : Type u} {m : (α : Type) → [MeasurableSpace α] → Type w}
    [MeasurableSpaceMonad m] (p : α → m Bool) (as : Array α) (start := 0) (stop := as.size) : m
    Bool :=
  let rec @[specialize, nolint docBlame] any (i : USize) (stop : USize) : m Bool := rdo
    if i == stop then
      mPure false
    else
      if (← p (as.uget i lcProof)) then
        mPure true
      else
        any (i+1) stop
  if start < stop then
    let stop' := min stop as.size
    if start < stop' then
      any (USize.ofNat start) (USize.ofNat stop')
    else
      mPure false
  else
    mPure false

/-- Returns `true` if the measurable space monadic predicate `p` returns `true` for any element of
`as`. Analogue of core's `Array.anyM`.

Short-circuits upon encountering the first `true`. The elements in `as` are examined in order from
left to right.

The optional parameters `start` and `stop` control the region of the array to be checked. Only the
elements with indices from `start` (inclusive) to `stop` (exclusive) are checked. By default, the
entire array is checked. -/
@[implemented_by mAnyMUnsafe]
def mAnyM {α : Type u} {m : (α : Type) → [MeasurableSpace α] → Type w} [MeasurableSpaceMonad m]
    (p : α → m Bool) (as : Array α) (start := 0) (stop := as.size) : m Bool :=
  let any (stop : Nat) (h : stop ≤ as.size) :=
    let rec loop (j : Nat) : m Bool := rdo
      if hlt : j < stop then
        have : j < as.size := Nat.lt_of_lt_of_le hlt h
        if (← p as[j]) then
          mPure true
        else
          loop (j+1)
      else
        mPure false
      decreasing_by decreasing_trivial_pre_omega
    loop start
  if h : stop ≤ as.size then
    any stop h
  else
    any as.size (Nat.le_refl _)

/-- Returns `true` if the measurable space monadic predicate `p` returns `true` for every element of
`as`. Analogue of core's `Array.allM`.

Short-circuits upon encountering the first `false`. The elements in `as` are examined in order from
left to right.

The optional parameters `start` and `stop` control the region of the array to be checked. Only the
elements with indices from `start` (inclusive) to `stop` (exclusive) are checked. By default, the
entire array is checked. -/
@[inline]
def mAllM {α : Type u} {m : (α : Type) → [MeasurableSpace α] → Type w} [MeasurableSpaceMonad m]
    (p : α → m Bool) (as : Array α) (start := 0) (stop := as.size) : m Bool :=
  rdo return !(← as.mAnyM (start := start) (stop := stop) fun v => rdo return !(← p v))

/-- Returns the first non-`none` result of applying the measurable space monadic function `f` to
each element of the array in reverse order, from right to left. Once a non-`none` result is found,
no further elements are checked. Returns `none` if `f` returns `none` for all elements of the array.
Analogue of core's `Array.findSomeRevM?`. -/
@[inline]
def mFindSomeRevM? {α : Type u} {β : Type v} {m : (α : Type v) → [MeasurableSpace α] → Type w}
    [MeasurableSpaceMonad m] [MeasurableSpace β] (f : α → m (Option β)) (as : Array α) : m
    (Option β) :=
  let rec @[specialize, nolint docBlame] find : (i : Nat) → i ≤ as.size → m (Option β)
    | 0,   _ => mPure none
    | i+1, h => rdo
      have : i < as.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h
      let r ← f as[i]
      match r with
      | some _ => mPure r
      | none   =>
        have : i ≤ as.size := Nat.le_of_lt this
        find i this
  find as.size (Nat.le_refl _)

/-- Returns the last element of the array for which the measurable space monadic predicate `p`
returns `true`, or `none` if no such element is found. Elements of the array are checked in reverse,
from right to left. Analogue of core's `Array.findRevM?`.

The monad `m` takes value types in `Type` to avoid needing to use `ULift Bool` in `p`'s type. -/
@[inline]
def mFindRevM? {α : Type} [MeasurableSpace α] {m : (α : Type) → [MeasurableSpace α] → Type w}
    [MeasurableSpaceMonad m] (p : α → m Bool) (as : Array α) : m (Option α) :=
  as.mFindSomeRevM? fun a => rdo return if (← p a) then some a else none

/-- Applies the measurable space monadic action `f` to each element of an array, in order. Analogue
of core's `Array.forM`.

The optional parameters `start` and `stop` control the region of the array to which `f` should be
applied. Iteration proceeds from `start` (inclusive) to `stop` (exclusive), so `f` is not invoked
unless `start < stop`. By default, the entire array is used. -/
@[inline]
protected def mForM {α : Type u} {m : (α : Type v) → [MeasurableSpace α] → Type w}
    [MeasurableSpaceMonad m] (f : α → m PUnit) (as : Array α) (start := 0) (stop := as.size) : m
    PUnit :=
  as.mFoldlM (fun _ => f) ⟨⟩ start stop

/-- Applies a measurable space monadic function that returns an array to each element of an array,
from left to right. The resulting arrays are appended. Analogue of core's `Array.flatMapM`. -/
@[inline]
def mFlatMapM {α : Type u} {β : Type v} [MeasurableSpace β]
    {m : (γ : Type v) → [MeasurableSpace γ] → Type w} [MeasurableSpaceMonad m]
    (f : α → m (Array β)) (as : Array α) : m (Array β) :=
  as.mFoldlM (init := empty) fun bs a => rdo return bs ++ (← f a)

/-- Applies the measurable space monadic predicate `p` to every element in the array, in order from
left to right, and returns the array of elements for which `p` returns `true`. Analogue of core's
`Array.filterM`.

Only elements from `start` (inclusive) to `stop` (exclusive) are considered. Elements outside that
range are discarded. By default, the entire array is checked. -/
@[inline]
def mFilterM {α : Type} [MeasurableSpace α] {m : (γ : Type) → [MeasurableSpace γ] → Type w}
    [MeasurableSpaceMonad m] (p : α → m Bool) (as : Array α) (start := 0) (stop := as.size) : m
    (Array α) :=
  as.mFoldlM (init := #[]) (start := start) (stop := stop) fun acc a => rdo
    if (← p a) then return acc.push a else return acc

/-- Applies the measurable space monadic predicate `p` to every element in the array in reverse
order, from right to left, and returns those elements for which `p` returns `true`. The elements of
the returned array are in the same order as in the input array. Analogue of core's
`Array.filterRevM`.

Only elements from `start` (exclusive) to `stop` (inclusive) are considered. Elements outside that
range are discarded. Because the array is examined in reverse order, elements are only examined when
`start > stop`. By default, the entire array is considered. -/
@[inline]
def mFilterRevM {α : Type} [MeasurableSpace α] {m : (γ : Type) → [MeasurableSpace γ] → Type w}
    [MeasurableSpaceMonad m] (p : α → m Bool) (as : Array α) (start := as.size) (stop := 0) : m
    (Array α) :=
  reverse <$>ₘ as.mFoldrM (init := #[]) (start := start) (stop := stop) fun a acc => rdo
    if (← p a) then return acc.push a else return acc

/-- Applies a measurable space monadic function that returns an `Option` to each element of an
array, collecting the non-`none` values. Analogue of core's `Array.filterMapM`.

Only elements from `start` (inclusive) to `stop` (exclusive) are considered. Elements outside that
range are discarded. By default, the entire array is considered. -/
@[specialize]
def mFilterMapM {α : Type u} {β : Type v} [MeasurableSpace β]
    {m : (γ : Type v) → [MeasurableSpace γ] → Type w} [MeasurableSpaceMonad m]
    (f : α → m (Option β)) (as : Array α) (start := 0) (stop := as.size) : m (Array β) :=
  as.mFoldlM (init := #[]) (start := start) (stop := stop) fun bs a => rdo
    match (← f a) with
    | some b => mPure (bs.push b)
    | none   => mPure bs

/-- Accumulator loop for `mZipWithM`. Analogue of core's `Array.zipWithMAux`. -/
@[specialize]
def mZipWithMAux {α : Type u} {β : Type x} {γ : Type v} [MeasurableSpace γ]
    {m : (α : Type v) → [MeasurableSpace α] → Type w} [MeasurableSpaceMonad m] (as : Array α)
    (bs : Array β) (f : α → β → m γ) (i : Nat) (cs : Array γ) : m (Array γ) := rdo
  if h : i < as.size then
    let a := as[i]
    if h : i < bs.size then
      let b := bs[i]
      mZipWithMAux as bs f (i+1) <| cs.push (← f a b)
    else
      return cs
  else
    return cs
decreasing_by decreasing_trivial_pre_omega

/-- Applies a measurable space monadic function to the corresponding elements of two arrays,
left-to-right, stopping at the end of the shorter array. `mZipWithM f as bs` is equivalent to
`mMapM id (zipWith f as bs)`. Analogue of core's `Array.zipWithM`. -/
@[inline] def mZipWithM {α : Type u} {β : Type x} {γ : Type v} [MeasurableSpace γ]
    {m : (α : Type v) → [MeasurableSpace α] → Type w} [MeasurableSpaceMonad m] (f : α → β → m γ)
    (as : Array α) (bs : Array β) : m (Array γ) :=
  mZipWithMAux as bs f 0 #[]

/-! ## Array-to-list correspondence for folds -/

variable {α : Type u} {β : Type v} [MeasurableSpace β]
  {m : (γ : Type v) → [MeasurableSpace γ] → Type w} [MeasurableSpaceMonad m]

theorem mFoldlM_toList.aux {f : β → α → m β} {xs : Array α} {i j} (H : xs.size ≤ i + j) {b : β} :
    mFoldlM.loop f xs xs.size (Nat.le_refl _) i j b = (xs.toList.drop j).mFoldlM f b := by
  unfold mFoldlM.loop
  split
  · split
    · cases Nat.not_le_of_gt ‹_› (Nat.zero_add _ ▸ H)
    · rename_i i
      rw [Nat.succ_add] at H
      simp only [mFoldlM_toList.aux (j := j+1) H]
      rw (occs := [2]) [← List.getElem_cons_drop ‹_›]
      simp
  · rw [List.drop_of_length_le (Nat.ge_of_not_lt ‹_›)]; simp

@[simp, grind =] theorem mFoldlM_toList {f : β → α → m β} {init : β} {xs : Array α} :
    xs.toList.mFoldlM f init = xs.mFoldlM f init := by
  simp [mFoldlM, mFoldlM_toList.aux]

theorem mFoldrM_eq_reverse_foldlM_toList.aux {f : α → β → m β} {xs : Array α} {init : β} {i} (h) :
    (xs.toList.take i).reverse.mFoldlM (fun x y => f y x) init = mFoldrM.fold f xs 0 i h init := by
  unfold mFoldrM.fold
  match i with
  | 0 => simp
  | i+1 =>
    rw [← List.take_concat_get h]; simp [← aux]

theorem mFoldrM_eq_reverse_foldlM_toList {f : α → β → m β} {init : β} {xs : Array α} :
    xs.mFoldrM f init = xs.toList.reverse.mFoldlM (fun x y => f y x) init := by
  rcases xs with ⟨_ | ⟨a, l⟩⟩ <;>
    simp [mFoldrM, ← mFoldrM_eq_reverse_foldlM_toList.aux]

@[simp, grind =] theorem mFoldrM_toList {f : α → β → m β} {init : β} {xs : Array α} :
    xs.toList.mFoldrM f init = xs.mFoldrM f init := by
  rw [mFoldrM_eq_reverse_foldlM_toList, List.mFoldlM_reverse]

theorem mFoldlM_start_stop {xs : Array α} {f : β → α → m β} {b : β} {start stop : Nat} :
    xs.mFoldlM f b start stop = (xs.extract start stop).mFoldlM f b := by
  unfold mFoldlM
  simp only [Nat.sub_zero, size_extract, Nat.le_refl, ↓reduceDIte]
  suffices mFoldlM.loop f xs (min stop xs.size) (by omega) (min stop xs.size - start) start b =
      mFoldlM.loop f (xs.extract start stop) (min stop xs.size - start) (by simp)
        (min stop xs.size - start) 0 b by
    split
    · have : min stop xs.size = stop := by omega
      simp_all
    · have : min stop xs.size = xs.size := by omega
      simp_all
  revert b
  suffices ∀ (b : β) (i k) (w : i + k = min stop xs.size - start),
    mFoldlM.loop f xs (min stop xs.size) (by omega) i (start + k) b =
      mFoldlM.loop f (xs.extract start stop) (min stop xs.size - start) (by simp) i k b by
    intro b
    simpa using this b (min stop xs.size - start) 0 (by omega)
  intro b i k w
  induction i generalizing b k with
  | zero =>
    simp only [Nat.zero_add] at w
    subst k
    simp [mFoldlM.loop]
  | succ i ih =>
    unfold mFoldlM.loop
    rw [dite_eq_left (by omega), dite_eq_left (by omega)]
    split <;> rename_i h
    · rfl
    · simp only [Nat.succ_eq_add_one, Nat.add_right_cancel_iff] at h
      subst h
      simp only [getElem_extract]
      apply MeasurableSpaceBind.bind_congr
      intro b
      simpa [Nat.add_assoc] using ih b (k + 1) (by omega)

theorem mFoldrM_start_stop {xs : Array α} {f : α → β → m β} {b : β} {start stop : Nat} :
    xs.mFoldrM f b start stop = (xs.extract stop start).mFoldrM f b := by
  unfold mFoldrM
  simp only [size_extract, Nat.le_refl, ↓reduceDIte]
  suffices stop ≤ min start xs.size →
      mFoldrM.fold f xs stop (min start xs.size) (by omega) b =
        mFoldrM.fold f (xs.extract stop start) 0 (min start xs.size - stop) (by simp) b by
    split
    · split
      · rw [ite_eq_left (by omega)]
        have h : min start xs.size = start := by omega
        specialize this (by omega)
        simp_all
      · rw [ite_eq_right (by omega)]
    · split
      · rw [ite_eq_left (by omega)]
        have h : min start xs.size = xs.size := by omega
        specialize this (by omega)
        simp_all
      · rw [ite_eq_right (by omega)]
  revert b
  suffices ∀ (b : β) (i) (w : stop + i ≤ min start xs.size),
      mFoldrM.fold f xs stop (stop + i) (by omega) b =
        mFoldrM.fold f (xs.extract stop start) 0 i (by simp; omega) b by
    intro b w
    specialize this b (min start xs.size - stop)
    have h : stop + (min start xs.size - stop) = min start xs.size := by omega
    simp_all
  intro b i w
  induction i generalizing b with
  | zero =>
    unfold mFoldrM.fold
    simp
  | succ i ih =>
    unfold mFoldrM.fold
    simp only [beq_iff_eq, Nat.add_eq_left, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_eq,
      getElem_extract]
    apply MeasurableSpaceBind.bind_congr
    intro b
    exact ih b (by omega)

@[simp] theorem _root_.List.mFoldlM_toArray {l : List α} {f : β → α → m β} {b : β} :
    l.toArray.mFoldlM f b = l.mFoldlM f b :=
  Array.mFoldlM_toList.symm

@[simp] theorem _root_.List.mFoldlM_toArray' {l : List α} {f : β → α → m β}
    {b : β} {stop : Nat} (w : stop = l.length) :
    l.toArray.mFoldlM f b 0 stop = l.mFoldlM f b := by
  subst w
  exact List.mFoldlM_toArray

@[simp] theorem _root_.List.mFoldrM_toArray {l : List α} {f : α → β → m β} {b : β} :
    l.toArray.mFoldrM f b = l.mFoldrM f b :=
  Array.mFoldrM_toList.symm

@[simp] theorem _root_.List.mFoldrM_toArray' {l : List α} {f : α → β → m β}
    {b : β} {start : Nat} (w : start = l.length) :
    l.toArray.mFoldrM f b start 0 = l.mFoldrM f b := by
  subst w
  exact List.mFoldrM_toArray

theorem mFoldlM_eq_mFoldlM_toList {xs : Array α} {f : β → α → m β} {b : β}
    {start stop : Nat} :
    xs.mFoldlM f b start stop = (xs.toList.extract start stop).mFoldlM f b := by
  rw [mFoldlM_start_stop, ← mFoldlM_toList, toList_extract]

theorem mFoldrM_eq_mFoldrM_toList {xs : Array α} {f : α → β → m β} {b : β}
    {start stop : Nat} :
    xs.mFoldrM f b start stop = (xs.toList.extract stop start).mFoldrM f b := by
  rw [mFoldrM_start_stop, ← mFoldrM_toList, toList_extract]

section Lawful

variable [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)] [LawfulMeasurableSpaceMonad m]

@[fun_prop] theorem measurable_mFoldlM (xs : Array α) {f : β → α → m β}
    (hf : ∀ a, Measurable (fun b => f b a)) (start stop : Nat) :
    Measurable (fun b => xs.mFoldlM f b start stop) := by
  simp_rw [mFoldlM_eq_mFoldlM_toList]
  fun_prop

@[fun_prop] theorem measurable_mFoldrM (xs : Array α) {f : α → β → m β}
    (hf : ∀ a, Measurable (f a)) (start stop : Nat) :
    Measurable (fun b => xs.mFoldrM f b start stop) := by
  simp_rw [mFoldrM_eq_mFoldrM_toList]
  fun_prop

end Lawful

section Map

variable [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)]

private theorem measurable_push_of_measurable_cons [LawfulMeasurableSpaceMonad m] {f : α → m β}
    (hf : ∀ a, Measurable (fun bs : List β => (fun b => b :: bs) <$>ₘ f a)) (a : α) :
    Measurable (fun bs : Array β => (fun b => bs.push b) <$>ₘ f a) := by
  simpa (disch := fun_prop) [Function.comp_def, ← toList_push] using
    (measurable_mMap (f := m) (g := fun bs : List β => bs.reverse.toArray) (by fun_prop)).comp
      ((hf a).comp (measurable_list_reverse.comp measurable_toList))

theorem mMapM_eq_mFoldlM [LawfulMeasurableSpaceMonad m] {f : α → m β} {xs : Array α}
    (hf : ∀ a, Measurable (fun bs : Array β => (fun b => bs.push b) <$>ₘ f a)) :
    xs.mMapM f = xs.mFoldlM (fun bs a => bs.push <$>ₘ f a) #[] := by
  rw [mMapM, aux, ← mFoldlM_toList]
  rfl
where
  aux (i bs) :
      mMapM.map f xs i bs = (xs.toList.drop i).mFoldlM (fun bs a => bs.push <$>ₘ f a) bs := by
    unfold mMapM.map
    split
    · rw [← List.getElem_cons_drop ‹_›]
      simp (disch := fun_prop) [aux (i + 1), mBind_mMap_left]
    · rw [List.drop_of_length_le (Nat.ge_of_not_lt ‹_›)]
      rfl
  termination_by xs.size - i
  decreasing_by decreasing_trivial_pre_omega

omit [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)] in
@[simp] theorem mMapM_empty (f : α → m β) : mMapM f #[] = mPure #[] := by
  simp [mMapM, mMapM.map]

theorem mMapM_eq_mMapM_toList [LawfulMeasurableSpaceMonad m] {f : α → m β} {xs : Array α}
    (hf : ∀ a, Measurable (fun bs : List β => (fun b => b :: bs) <$>ₘ f a)) :
    xs.mMapM f = List.toArray <$>ₘ xs.toList.mMapM f := by
  rw [mMapM_eq_mFoldlM (measurable_push_of_measurable_cons hf), ← mFoldlM_toList,
    List.mMapM_eq_reverse_mFoldlM_cons hf]
  simp (disch := fun_prop) only [mMap_mMap]
  suffices h : ∀ (l : List α) (bs : List β),
      l.mFoldlM (fun acc a => acc.push <$>ₘ f a) bs.reverse.toArray =
        (fun bs : List β => bs.reverse.toArray) <$>ₘ
          l.mFoldlM (fun acc a => (· :: acc) <$>ₘ f a) bs from h xs.toList []
  intro l bs
  induction l generalizing bs with
  | nil => simp (disch := fun_prop)
  | cons a l ih =>
    have hpush := measurable_push_of_measurable_cons hf
    simp (disch := fun_prop) only [List.mFoldlM_cons, mBind_mMap_left, mMap_mBind]
    apply MeasurableSpaceBind.bind_congr
    intro b
    simpa using ih (b :: bs)

@[simp] theorem toList_mMapM [LawfulMeasurableSpaceMonad m] {f : α → m β} {xs : Array α}
    (hf : ∀ a, Measurable (fun bs : List β => (fun b => b :: bs) <$>ₘ f a)) :
    toList <$>ₘ xs.mMapM f = xs.toList.mMapM f := by
  simp (disch := fun_prop) [mMapM_eq_mMapM_toList hf]

@[simp] theorem _root_.List.mMapM_toArray [LawfulMeasurableSpaceMonad m] {f : α → m β} {l : List α}
    (hf : ∀ a, Measurable (fun bs : List β => (fun b => b :: bs) <$>ₘ f a)) :
    l.toArray.mMapM f = List.toArray <$>ₘ l.mMapM f :=
  Array.mMapM_eq_mMapM_toList hf

theorem mMap_toList_inj [LawfulMeasurableSpaceMonad m] {xs ys : m (Array β)} :
    toList <$>ₘ xs = toList <$>ₘ ys ↔ xs = ys := by
  constructor
  · intro h
    simpa (disch := fun_prop) using congrArg (fun x : m (List β) => List.toArray <$>ₘ x) h
  · rintro rfl
    rfl

@[simp] theorem mMapM_pure [LawfulMeasurableSpaceMonad m] {xs : Array α} {f : α → β} :
    xs.mMapM (m := m) (mPure <| f ·) = mPure (xs.map f) := by
  have hf : ∀ a, Measurable (fun bs : List β =>
      (fun b => b :: bs) <$>ₘ (mPure (f a) : m β)) := by
    intro a
    simp (disch := fun_prop) only [mMap_mPure]
    fun_prop
  simp (disch := fun_prop) [mMapM_eq_mMapM_toList hf, ← List.map_toArray]

@[simp] theorem mMapM_map [LawfulMeasurableSpaceMonad m] {α' : Type x} {f : α → α'} {g : α' → m β}
    {xs : Array α}
    (hg : ∀ a, Measurable (fun bs : List β => (fun b => b :: bs) <$>ₘ g a)) :
    (xs.map f).mMapM g = xs.mMapM (g ∘ f) := by
  rw [mMapM_eq_mMapM_toList hg, mMapM_eq_mMapM_toList (f := g ∘ f) (fun a => hg (f a))]
  simp

theorem mMapM_append [LawfulMeasurableSpaceMonad m] {xs ys : Array α} {f : α → m β}
    (hf : ∀ a, Measurable (fun bs : List β => (fun b => b :: bs) <$>ₘ f a)) :
    (xs ++ ys).mMapM f = (rdo return (← xs.mMapM f) ++ (← ys.mMapM f)) := by
  have h : Measurable (fun acc : Array β =>
      (fun bs : List β => acc ++ bs.toArray) <$>ₘ ys.toList.mMapM f) := by
    simpa (disch := fun_prop) [Function.comp_def, ← List.append_toArray] using
      (measurable_mMap (f := m) measurable_list_toArray).comp
        ((List.measurable_append_mMapM ys.toList hf).comp measurable_toList)
  rw [mMapM_eq_mMapM_toList hf, toList_append, List.mMapM_append hf]
  simp (disch := fun_prop) [mMapM_eq_mMapM_toList hf, ← List.append_toArray]

theorem mMapM_eq_mFoldlM_push [LawfulMeasurableSpaceMonad m] {f : α → m β} {xs : Array α}
    (hf : ∀ a, Measurable (fun bs : Array β => (fun b => bs.push b) <$>ₘ f a)) :
    xs.mMapM f = xs.mFoldlM (fun acc a => rdo return acc.push (← f a)) #[] := by
  simpa (disch := fun_prop) using mMapM_eq_mFoldlM (xs := xs) hf

end Map

theorem mFoldlM_map {α' : Type x} {f : α → α'} {g : β → α' → m β}
    {xs : Array α} {init : β} {stop : Nat} (w : stop = xs.size) :
    (xs.map f).mFoldlM g init 0 stop = xs.mFoldlM (fun x y => g x (f y)) init 0 stop := by
  subst w
  simp [mFoldlM_eq_mFoldlM_toList, List.extract, ← List.map_take, List.mFoldlM_map]

theorem mFoldrM_map {α' : Type x} {f : α → α'} {g : α' → β → m β}
    {xs : Array α} {init : β} {start : Nat} (w : start = xs.size) :
    (xs.map f).mFoldrM g init start 0 = xs.mFoldrM (fun x y => g (f x) y) init start 0 := by
  subst w
  simp [mFoldrM_eq_mFoldrM_toList, List.extract, ← List.map_take, List.mFoldrM_map]

section Fold

variable [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)] [LawfulMeasurableSpaceMonad m]

theorem mFoldlM_append {f : β → α → m β} {b : β} {xs ys : Array α}
    (hf : ∀ a, Measurable (fun b => f b a)) :
    (xs ++ ys).mFoldlM f b = xs.mFoldlM f b >>=ₘ ys.mFoldlM f := by
  simp only [← mFoldlM_toList, toList_append]
  exact List.mFoldlM_append hf

theorem mFoldrM_append {f : α → β → m β} {b : β} {xs ys : Array α}
    (hf : ∀ a, Measurable (f a)) :
    (xs ++ ys).mFoldrM f b = ys.mFoldrM f b >>=ₘ xs.mFoldrM f := by
  simp only [← mFoldrM_toList, toList_append]
  exact List.mFoldrM_append hf

@[simp] theorem mFoldlM_pure {f : β → α → β} {b : β} {xs : Array α} {start stop : Nat}
    (hf : ∀ a, Measurable (fun b => f b a)) :
    xs.mFoldlM (m := m) (mPure <| f · ·) b start stop =
      mPure (xs.foldl f b start stop) := by
  rw [mFoldlM_eq_mFoldlM_toList, List.mFoldlM_pure hf]
  rw [foldl, foldlM_start_stop, ← foldlM_toList, List.foldlM_pure]
  simp

@[simp] theorem mFoldrM_pure {f : α → β → β} {b : β} {xs : Array α} {start stop : Nat}
    (hf : ∀ a, Measurable (f a)) :
    xs.mFoldrM (m := m) (mPure <| f · ·) b start stop =
      mPure (xs.foldr f b start stop) := by
  rw [mFoldrM_eq_mFoldrM_toList, List.mFoldrM_pure hf]
  rw [foldr, foldrM_start_stop, ← foldrM_toList, List.foldrM_pure]
  simp

theorem mFoldlM_filterMap {α' : Type x} {f : α → Option α'} {g : β → α' → m β}
    {xs : Array α} {init : β} {stop : Nat} (w : stop = (xs.filterMap f).size)
    (hg : ∀ a, Measurable (fun b => g b a)) :
    (xs.filterMap f).mFoldlM g init 0 stop =
      xs.mFoldlM (fun x y => match f y with | some b => g x b | none => mPure x) init := by
  subst w
  simp only [← mFoldlM_toList, toList_filterMap]
  exact List.mFoldlM_filterMap hg

theorem mFoldrM_filterMap {α' : Type x} {f : α → Option α'} {g : α' → β → m β}
    {xs : Array α} {init : β} {start : Nat} (w : start = (xs.filterMap f).size)
    (hg : ∀ a, Measurable (g a)) :
    (xs.filterMap f).mFoldrM g init start 0 =
      xs.mFoldrM (fun x y => match f x with | some b => g b y | none => mPure y) init := by
  subst w
  simp only [← mFoldrM_toList, toList_filterMap]
  exact List.mFoldrM_filterMap hg

theorem mFoldlM_filter {p : α → Bool} {g : β → α → m β} {xs : Array α}
    {init : β} {stop : Nat} (w : stop = (xs.filter p).size)
    (hg : ∀ a, Measurable (fun b => g b a)) :
    (xs.filter p).mFoldlM g init 0 stop =
      xs.mFoldlM (fun x y => if p y then g x y else mPure x) init := by
  subst w
  simp only [← mFoldlM_toList, toList_filter]
  exact List.mFoldlM_filter hg

theorem mFoldrM_filter {p : α → Bool} {g : α → β → m β} {xs : Array α}
    {init : β} {start : Nat} (w : start = (xs.filter p).size)
    (hg : ∀ a, Measurable (g a)) :
    (xs.filter p).mFoldrM g init start 0 =
      xs.mFoldrM (fun x y => if p x then g x y else mPure y) init := by
  subst w
  simp only [← mFoldrM_toList, toList_filter]
  exact List.mFoldrM_filter hg

end Fold

section Indexed

variable [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)]

-- Measurability of core's indexed accumulator loop, with the index and its bound fixed.
@[fun_prop] private theorem measurable_mMapFinIdxM_map [LawfulMeasurableSpaceMonad m] (xs : Array α)
    (f : (i : Nat) → α → i < xs.size → m β)
    (hf : ∀ i h a, Measurable (fun bs : Array β => (fun b => bs.push b) <$>ₘ f i a h))
    (i j : Nat) (inv : i + j = xs.size) :
    Measurable (mMapFinIdxM.map xs f i j inv) := by
  induction i generalizing j with
  | zero => simp only [mMapFinIdxM.map]; fun_prop
  | succ i ih =>
    simp only [mMapFinIdxM.map]
    have hj : j < xs.size := by omega
    have hrec := ih (j + 1) (by omega)
    simpa (disch := fun_prop) [Function.comp_def] using
      (measurable_mBind hrec).comp (hf j hj xs[j])

theorem toList_mMapFinIdxM [LawfulMeasurableSpaceMonad m] {xs : Array α}
    {f : (i : Nat) → α → i < xs.size → m β}
    (hf : ∀ i h a, Measurable (fun bs : Array β => (fun b => bs.push b) <$>ₘ f i a h)) :
    toList <$>ₘ xs.mMapFinIdxM f = xs.toList.mMapFinIdxM f := by
  let rec go (i : Nat) (acc : Array β) (inv : i + acc.size = xs.size) :
      toList <$>ₘ mMapFinIdxM.map xs f i acc.size inv acc =
        List.mMapFinIdxM.go xs.toList f (xs.toList.drop acc.size) acc (by simp; omega) := by
    match i with
    | 0 =>
      have h : acc.size = xs.size := by omega
      simp (disch := fun_prop) [mMapFinIdxM.map, h, ← length_toList, List.mMapFinIdxM.go]
    | k + 1 =>
      conv => rhs; arg 3; rw [← List.getElem_cons_drop (by simp; omega)]
      simp only [mMapFinIdxM.map, List.mMapFinIdxM.go, getElem_toList]
      rw [mMap_mBind (by fun_prop) _ (by fun_prop)]
      apply MeasurableSpaceBind.bind_congr
      intro b
      simpa using go k (acc.push b) (by simp; omega)
  exact go xs.size #[] (by simp)

theorem _root_.List.mMapFinIdxM_toArray [LawfulMeasurableSpaceMonad m] {l : List α}
    {f : (i : Nat) → α → i < l.length → m β}
    (hf : ∀ i h a, Measurable (fun bs : Array β => (fun b => bs.push b) <$>ₘ f i a h)) :
    l.toArray.mMapFinIdxM f = List.toArray <$>ₘ l.mMapFinIdxM f := by
  apply Array.mMap_toList_inj.mp
  simp (disch := fun_prop) [Array.toList_mMapFinIdxM hf]

theorem _root_.List.mMapIdxM_toArray [LawfulMeasurableSpaceMonad m] {l : List α} {f : Nat → α → m β}
    (hf : ∀ i a, Measurable (fun bs : Array β => (fun b => bs.push b) <$>ₘ f i a)) :
    l.toArray.mMapIdxM f = List.toArray <$>ₘ l.mMapIdxM f := by
  have go (bs : List α) (acc : Array β) (inv : bs.length + acc.size = l.length) :
      List.mMapFinIdxM.go l (fun i a _ => f i a) bs acc inv = List.mMapIdxM.go f bs acc := by
    induction bs generalizing acc with
    | nil => rfl
    | cons a bs ih => simp [List.mMapFinIdxM.go, List.mMapIdxM.go, ih]
  unfold mMapIdxM
  refine (List.mMapFinIdxM_toArray (l := l) (f := fun i a _ => f i a)
    (fun i _ a => hf i a)).trans ?_
  simp [List.mMapFinIdxM, List.mMapIdxM, go]

theorem toList_mMapIdxM [LawfulMeasurableSpaceMonad m] {xs : Array α} {f : Nat → α → m β}
    (hf : ∀ i a, Measurable (fun bs : Array β => (fun b => bs.push b) <$>ₘ f i a)) :
    toList <$>ₘ xs.mMapIdxM f = xs.toList.mMapIdxM f := by
  rw [← toArray_toList (xs := xs), List.mMapIdxM_toArray hf]
  simp (disch := fun_prop)

end Indexed

end Array

namespace Array

section Predicates

universe u w
variable {α : Type u} {m : (γ : Type) → [MeasurableSpace γ] → Type w} [MeasurableSpaceMonad m]

theorem mAnyM_eq_mAnyM_loop {p : α → m Bool} {as : Array α} {start stop} :
    mAnyM p as start stop = mAnyM.loop p as (min stop as.size) (Nat.min_le_right ..) start := by
  simp only [mAnyM, Nat.min_def]; split <;> rfl

theorem mAnyM_stop_le_start {p : α → m Bool} {as : Array α} {start stop}
    (h : min stop as.size ≤ start) : mAnyM p as start stop = mPure false := by
  rw [mAnyM_eq_mAnyM_loop, mAnyM.loop, dite_eq_right (Nat.not_lt.2 h)]

theorem mAnyM_loop_cons {p : α → m Bool} {a : α} {as : List α} {stop start : Nat}
    (h : stop + 1 ≤ (a :: as).length) :
    mAnyM.loop p ⟨a :: as⟩ (stop + 1) h (start + 1) =
      mAnyM.loop p ⟨as⟩ stop (by simpa using h) start := by
  rw [mAnyM.loop]
  conv => rhs; rw [mAnyM.loop]
  split <;> rename_i h'
  · simp only [Nat.add_lt_add_iff_right] at h'
    rw [dite_eq_left h', mAnyM_loop_cons]
    simp
  · rw [dite_eq_right]
    omega

@[simp, grind =] theorem mAnyM_toList {p : α → m Bool} {as : Array α} :
    as.toList.mAnyM p = as.mAnyM p :=
  match as with
  | ⟨[]⟩  => by simp [mAnyM, mAnyM.loop]
  | ⟨a :: as⟩ => by
    simp only [List.mAnyM, mAnyM, List.size_toArray, List.length_cons, Nat.le_refl, ↓reduceDIte]
    rw [mAnyM.loop, dite_eq_left (by omega)]
    congr 1
    funext b
    split
    · simp
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [mAnyM_loop_cons]
      simpa [mAnyM] using (mAnyM_toList (as := as.toArray) (p := p))

@[simp] theorem _root_.List.mAnyM_toArray {p : α → m Bool} {l : List α} :
    l.toArray.mAnyM p = l.mAnyM p := mAnyM_toList.symm

variable [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)] [LawfulMeasurableSpaceMonad m]

theorem mAllM_eq_not_mAnyM_not {p : α → m Bool} {as : Array α} :
    mAllM p as = (! ·) <$>ₘ mAnyM ((! ·) <$>ₘ p ·) as := by
  simp (disch := fun_prop) [mAllM]

@[simp] theorem mAllM_toList {p : α → m Bool} {as : Array α} :
    as.toList.mAllM p = as.mAllM p := by
  rw [mAllM_eq_not_mAnyM_not, ← mAnyM_toList, List.mAllM_eq_not_mAnyM_not]

@[simp] theorem _root_.List.mAllM_toArray {p : α → m Bool} {l : List α} :
    l.toArray.mAllM p = l.mAllM p := mAllM_toList.symm

@[simp] theorem mAnyM_pure {p : α → Bool} {xs : Array α} :
    xs.mAnyM (m := m) (mPure <| p ·) = mPure (xs.any p) := by
  rw [← mAnyM_toList, List.mAnyM_pure, any_toList]

@[simp] theorem mAllM_pure {p : α → Bool} {xs : Array α} :
    xs.mAllM (m := m) (mPure <| p ·) = mPure (xs.all p) := by
  rw [← mAllM_toList, List.mAllM_pure, all_toList]

end Predicates

end Array

namespace Array

universe u v w

section ForM

variable {α : Type u} {m : (γ : Type v) → [MeasurableSpace γ] → Type w}
  [MeasurableSpaceMonad m]

@[simp] theorem _root_.List.mForM_toArray (l : List α) (f : α → m PUnit) :
    l.toArray.mForM f = l.mForM f := by
  rw [Array.mForM, List.mFoldlM_toArray]
  induction l <;> simp_all [List.mForM]

theorem mForM_toList {xs : Array α} {f : α → m PUnit} :
    xs.toList.mForM f = xs.mForM f :=
  (List.mForM_toArray _ _).symm

theorem mForM_append
    [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)] [LawfulMeasurableSpaceMonad m]
    {xs ys : Array α} {f : α → m PUnit} :
    (xs ++ ys).mForM f = (rdo xs.mForM f; ys.mForM f) := by
  rw [← mForM_toList, toList_append, List.mForM_append, mForM_toList, mForM_toList]

theorem mForM_map {α' : Type*} {xs : Array α} {g : α → α'} {f : α' → m PUnit} :
    (xs.map g).mForM f = xs.mForM (fun a => f (g a)) := by
  rw [← mForM_toList, toList_map, List.mForM_map, mForM_toList]

end ForM

section FilterMap

variable {α : Type u} {β : Type v} [MeasurableSpace β]
  {m : (γ : Type v) → [MeasurableSpace γ] → Type w} [MeasurableSpaceMonad m]
  [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)] [LawfulMeasurableSpaceMonad m]

theorem _root_.List.mFilterMapM_toArray {l : List α} {f : α → m (Option β)}
    (hf : ∀ a, Measurable (fun bs : List β =>
      (fun b => match b with | none => bs | some b => b :: bs) <$>ₘ f a)) :
    l.toArray.mFilterMapM f = List.toArray <$>ₘ l.mFilterMapM f := by
  rw [mFilterMapM, List.mFoldlM_toArray]
  suffices h : ∀ (l : List α) (acc : List β),
      l.mFoldlM (fun bs a => rdo
        match ← f a with | some b => return bs.push b | none => return bs) acc.reverse.toArray =
      List.toArray <$>ₘ List.mFilterMapM.loop f l acc from h l []
  intro l acc
  induction l generalizing acc with
  | nil => simp (disch := fun_prop) [List.mFilterMapM.loop]
  | cons a l ih =>
    have hfold : Measurable (fun bs : Array β => l.mFoldlM (fun bs a => rdo
        match ← f a with | some b => return bs.push b | none => return bs) bs) := by
      have h : Measurable (fun bs : Array β =>
          List.toArray <$>ₘ List.mFilterMapM.loop f l bs.toList.reverse) := by fun_prop
      simpa [← ih] using h
    simp only [List.mFoldlM_cons, List.mFilterMapM.loop]
    rw [mMap_mBind (by fun_prop) _ (by fun_prop), mBind_assoc _ (by fun_prop) hfold]
    apply MeasurableSpaceBind.bind_congr
    intro b
    cases b <;> simp (disch := fun_prop) [ih, ← List.reverse_cons]

theorem toList_mFilterMapM {xs : Array α} {f : α → m (Option β)}
    (hf : ∀ a, Measurable (fun bs : List β =>
      (fun b => match b with | none => bs | some b => b :: bs) <$>ₘ f a)) :
    toList <$>ₘ xs.mFilterMapM f = xs.toList.mFilterMapM f := by
  rw [← toArray_toList (xs := xs), List.mFilterMapM_toArray hf]
  simp (disch := fun_prop)

theorem _root_.List.mFlatMapM_toArray {l : List α} {f : α → m (Array β)}
    (hf : ∀ a, Measurable (fun bs : List (List β) =>
      (fun b => b :: bs) <$>ₘ (toList <$>ₘ f a))) :
    l.toArray.mFlatMapM f = List.toArray <$>ₘ l.mFlatMapM (fun a => toList <$>ₘ f a) := by
  rw [mFlatMapM, List.mFoldlM_toArray]
  suffices h : ∀ (l : List α) (acc : List (List β)),
      l.mFoldlM (fun bs a => rdo return bs ++ (← f a)) acc.reverse.flatten.toArray =
        List.toArray <$>ₘ List.mFlatMapM.loop (fun a => toList <$>ₘ f a) l acc from h l []
  intro l acc
  induction l generalizing acc with
  | nil => simp (disch := fun_prop) [List.mFlatMapM.loop]
  | cons a l ih =>
    have hfold : Measurable (fun bs : Array β =>
        l.mFoldlM (fun bs a => rdo return bs ++ (← f a)) bs) := by
      have h : Measurable (fun bs : Array β =>
          List.toArray <$>ₘ List.mFlatMapM.loop (fun a => toList <$>ₘ f a) l [bs.toList]) := by
        fun_prop
      simpa [← ih] using h
    simp (disch := fun_prop) only [mBind_mPure_comp] at hfold
    simp (disch := fun_prop) only [List.mFoldlM_cons, List.mFlatMapM.loop,
      mBind_mPure_comp, mBind_mMap_left, mMap_mBind]
    apply MeasurableSpaceBind.bind_congr
    intro bs
    simpa (disch := fun_prop) [List.reverse_cons, List.flatten_append,
      ← Array.toArray_append] using ih (bs.toList :: acc)

theorem toList_mFlatMapM {xs : Array α} {f : α → m (Array β)}
    (hf : ∀ a, Measurable (fun bs : List (List β) =>
      (fun b => b :: bs) <$>ₘ (toList <$>ₘ f a))) :
    toList <$>ₘ xs.mFlatMapM f = xs.toList.mFlatMapM (fun a => toList <$>ₘ f a) := by
  rw [← toArray_toList (xs := xs), List.mFlatMapM_toArray hf]
  simp (disch := fun_prop)

end FilterMap

end Array

namespace Array

section Filtering

universe w
variable {α : Type} [MeasurableSpace α]
  {m : (γ : Type) → [MeasurableSpace γ] → Type w} [MeasurableSpaceMonad m]
  [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)] [LawfulMeasurableSpaceMonad m]

theorem _root_.List.mFilterM_toArray {l : List α} {p : α → m Bool}
    (hp : ∀ a, Measurable (fun bs : List α => (fun b => cond b (a :: bs) bs) <$>ₘ p a)) :
    l.toArray.mFilterM p = List.toArray <$>ₘ l.mFilterM p := by
  rw [mFilterM, List.mFoldlM_toArray, List.mFilterM]
  simp (disch := fun_prop) only [mBind_mPure_comp, mMap_mMap]
  suffices h : ∀ (l : List α) (acc : List α),
      l.mFoldlM (fun bs a => rdo if ← p a then return bs.push a else return bs)
        acc.reverse.toArray =
        (fun bs : List α => bs.reverse.toArray) <$>ₘ List.mFilterAuxM p l acc from h l []
  intro l acc
  induction l generalizing acc with
  | nil => simp (disch := fun_prop) [List.mFilterAuxM]
  | cons a l ih =>
    have hfold : Measurable (fun bs : Array α =>
        l.mFoldlM (fun bs a => rdo if ← p a then return bs.push a else return bs) bs) := by
      have h : Measurable (fun bs : Array α =>
          (fun bs : List α => bs.reverse.toArray) <$>ₘ
            List.mFilterAuxM p l bs.toList.reverse) := by fun_prop
      simpa [← ih] using h
    simp only [List.mFoldlM_cons, List.mFilterAuxM]
    rw [mMap_mBind (f := fun bs : List α => bs.reverse.toArray) (by fun_prop) _ (by fun_prop)]
    rw [mBind_assoc _ (by fun_prop) hfold]
    apply MeasurableSpaceBind.bind_congr
    intro b
    cases b <;> simp (disch := fun_prop) [ih, ← List.reverse_cons]

theorem toList_mFilterM {xs : Array α} {p : α → m Bool}
    (hp : ∀ a, Measurable (fun bs : List α => (fun b => cond b (a :: bs) bs) <$>ₘ p a)) :
    toList <$>ₘ xs.mFilterM p = xs.toList.mFilterM p := by
  rw [← toArray_toList (xs := xs), List.mFilterM_toArray hp]
  simp (disch := fun_prop)

theorem _root_.List.mFilterRevM_toArray {l : List α} {p : α → m Bool}
    (hp : ∀ a, Measurable (fun bs : List α => (fun b => cond b (a :: bs) bs) <$>ₘ p a)) :
    l.toArray.mFilterRevM p = List.toArray <$>ₘ l.mFilterRevM p := by
  rw [mFilterRevM, List.mFoldrM_toArray, List.mFoldrM]
  have h := List.mFilterM_toArray (l := l.reverse) hp
  simp only [mFilterM, List.mFoldlM_toArray, List.mFilterM] at h
  simp (disch := fun_prop) only [mBind_mPure_comp, mMap_mMap] at h
  rw [h]
  simp (disch := fun_prop) [List.mFilterRevM, ← List.reverse_toArray]

theorem toList_mFilterRevM {xs : Array α} {p : α → m Bool}
    (hp : ∀ a, Measurable (fun bs : List α => (fun b => cond b (a :: bs) bs) <$>ₘ p a)) :
    toList <$>ₘ xs.mFilterRevM p = xs.toList.mFilterRevM p := by
  rw [← toArray_toList (xs := xs), List.mFilterRevM_toArray hp]
  simp (disch := fun_prop)

end Filtering

end Array

namespace Array

universe u v w x

section Zip
variable {α : Type u} {α' : Type x} {β : Type v} [MeasurableSpace β]
  {m : (γ : Type v) → [MeasurableSpace γ] → Type w} [MeasurableSpaceMonad m]

-- Comparing the reference loops directly gives this structural identity without monad laws.
theorem mZipWithM_eq_mMapM_id_zipWith {f : α → α' → m β} {as : Array α} {bs : Array α'} :
    as.mZipWithM f bs = (as.zipWith f bs).mMapM id := by
  let rec go (i : Nat) (acc : Array β) :
      mZipWithMAux as bs f i acc = mMapM.map id (as.zipWith f bs) i acc := by
    rw [mZipWithMAux, mMapM.map]
    by_cases ha : i < as.size <;> by_cases hb : i < bs.size
    · simp only [ha, hb, ↓reduceDIte, size_zipWith, Nat.lt_min, true_and, getElem_zipWith, id_eq]
      apply MeasurableSpaceBind.bind_congr
      intro b
      exact go (i + 1) (acc.push b)
    all_goals simp [ha, hb]
    termination_by as.size - i
    decreasing_by omega
  exact go 0 #[]

variable [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)]

-- Measurability of the accumulator in core's zip loop.
@[fun_prop] private theorem measurable_mZipWithMAux [LawfulMeasurableSpaceMonad m] (as : Array α)
    (bs : Array α')
    (f : α → α' → m β)
    (hf : ∀ a b, Measurable (fun acc : Array β => (fun c => acc.push c) <$>ₘ f a b))
    (i : Nat) : Measurable (fun acc => mZipWithMAux as bs f i acc) := by
  unfold mZipWithMAux
  split
  · split
    · have ih := measurable_mZipWithMAux as bs f hf (i + 1)
      simpa (disch := fun_prop) [Function.comp_def] using
        (measurable_mBind ih).comp (hf as[i] bs[i])
    · fun_prop
  · fun_prop
termination_by as.size - i
decreasing_by omega

theorem toList_mZipWithM [LawfulMeasurableSpaceMonad m] {as : Array α} {bs : Array α'}
    {f : α → α' → m β}
    (hf : ∀ a b, Measurable (fun acc : Array β => (fun c => acc.push c) <$>ₘ f a b)) :
    toList <$>ₘ as.mZipWithM f bs = as.toList.mZipWithM f bs.toList := by
  let rec go (i : Nat) (acc : Array β) :
      toList <$>ₘ mZipWithMAux as bs f i acc =
        List.mZipWithM.loop f (as.toList.drop i) (bs.toList.drop i) acc := by
    rw [mZipWithMAux]
    split
    · split
      · rw [← List.getElem_cons_drop (as := as.toList) (i := i) (by assumption),
          ← List.getElem_cons_drop (as := bs.toList) (i := i) (by assumption)]
        simp only [List.mZipWithM.loop, getElem_toList]
        rw [mMap_mBind (by fun_prop) _ (by fun_prop)]
        apply MeasurableSpaceBind.bind_congr
        intro b
        exact go (i + 1) (acc.push b)
      · rw [List.drop_of_length_le (l := bs.toList) (by simpa using Nat.le_of_not_gt ‹¬ _›)]
        cases as.toList.drop i <;> simp (disch := fun_prop) [List.mZipWithM.loop]
    · rw [List.drop_of_length_le (l := as.toList) (by simpa using Nat.le_of_not_gt ‹¬ _›)]
      simp (disch := fun_prop) [List.mZipWithM.loop]
    termination_by as.size - i
    decreasing_by omega
  simpa [mZipWithM, List.mZipWithM] using go 0 #[]

theorem _root_.List.mZipWithM_toArray [LawfulMeasurableSpaceMonad m] {as : List α} {bs : List α'}
    {f : α → α' → m β}
    (hf : ∀ a b, Measurable (fun acc : Array β => (fun c => acc.push c) <$>ₘ f a b)) :
    as.toArray.mZipWithM f bs.toArray = List.toArray <$>ₘ as.mZipWithM f bs := by
  apply mMap_toList_inj.mp
  simp (disch := fun_prop) [toList_mZipWithM hf]

end Zip

end Array

namespace Array

universe u v w

section SearchCorrespondence
variable {α : Type u} {β : Type v} [MeasurableSpace β]
  {m : (γ : Type v) → [MeasurableSpace γ] → Type w} [MeasurableSpaceMonad m]

variable [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)] [LawfulMeasurableSpaceMonad m]

#check _root_.List.findSomeM?_toArray

@[simp] theorem _root_.List.mFindSomeM?_toArray (f : α → m (Option β)) (l : List α) :
    l.toArray.mFindSomeM? f = l.mFindSomeM? f := by
  rw [mFindSomeM?, List.mForIn_toArray]
  induction l with
  | nil => simp (disch := fun_prop) [Break.runK]
  | cons a l ih =>
    simp only [List.mForIn_cons, List.mFindSomeM?]
    simp (disch := fun_prop) only [mBind_assoc]
    apply MeasurableSpaceBind.bind_congr
    intro b
    cases b <;> simp (disch := fun_prop) [Break.runK, ih]

#check _root_.Array.findSomeM?_toList

@[simp] theorem mFindSomeM?_toList {f : α → m (Option β)} {xs : Array α} :
    xs.toList.mFindSomeM? f = xs.mFindSomeM? f :=
  (List.mFindSomeM?_toArray _ _).symm

#check _root_.List.findSomeRevM?_toArray

omit [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)] [LawfulMeasurableSpaceMonad m] in
theorem _root_.List.mFindSomeRevM?_toArray (f : α → m (Option β)) (l : List α) :
    l.toArray.mFindSomeRevM? f = l.reverse.mFindSomeM? f := by
  have go (i : Nat) (h : i ≤ l.length) :
      mFindSomeRevM?.find f l.toArray i h = (l.take i).reverse.mFindSomeM? f := by
    induction i with
    | zero => simp [mFindSomeRevM?.find]
    | succ i ih =>
      rw [mFindSomeRevM?.find, List.take_add_one, List.getElem?_eq_getElem (by omega)]
      simp only [ih, List.reverse_append]
      apply MeasurableSpaceBind.bind_congr
      intro b
      cases b <;> rfl
  simp [mFindSomeRevM?, go]

#check _root_.Array.findSomeM?_pure

@[simp] theorem mFindSomeM?_pure {f : α → Option β} {xs : Array α} :
    xs.mFindSomeM? (m := m) (mPure <| f ·) = mPure (xs.findSome? f) := by
  rw [← mFindSomeM?_toList, List.mFindSomeM?_pure, findSome?_toList]

end SearchCorrespondence

section Find
variable {α : Type} [MeasurableSpace α]
  {m : (γ : Type) → [MeasurableSpace γ] → Type w} [MeasurableSpaceMonad m]
  [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)] [LawfulMeasurableSpaceMonad m]

#check _root_.List.findM?_toArray

@[simp] theorem _root_.List.mFindM?_toArray (p : α → m Bool) (l : List α) :
    l.toArray.mFindM? p = l.mFindM? p := by
  rw [mFindM?, List.mForIn_toArray]
  induction l with
  | nil => simp (disch := fun_prop) [List.mFindM?, Break.runK]
  | cons a l ih =>
    simp only [List.mForIn_cons, List.mFindM?]
    simp (disch := fun_prop) only [mBind_assoc]
    apply MeasurableSpaceBind.bind_congr
    intro b
    cases b <;> simp (disch := fun_prop) [Break.runK, ih]

#check _root_.Array.findM?_toList

@[simp] theorem mFindM?_toList {p : α → m Bool} {xs : Array α} :
    xs.toList.mFindM? p = xs.mFindM? p := (List.mFindM?_toArray _ _).symm

#check _root_.List.findRevM?_toArray

theorem _root_.List.mFindRevM?_toArray (p : α → m Bool) (l : List α) :
    l.toArray.mFindRevM? p = l.reverse.mFindM? p := by
  rw [mFindRevM?, List.mFindSomeRevM?_toArray, List.mFindM?_eq_mFindSomeM?]

#check _root_.Array.findM?_pure

@[simp] theorem mFindM?_pure {p : α → Bool} {xs : Array α} :
    xs.mFindM? (m := m) (mPure <| p ·) = mPure (xs.find? p) := by
  rw [← mFindM?_toList, List.mFindM?_pure, find?_toList]

end Find

end Array

namespace Array

universe u v w
variable {α : Type u} {β : Type v} [MeasurableSpace β]
  {m : (γ : Type v) → [MeasurableSpace γ] → Type w} [MeasurableSpaceMonad m]

/-! ## Congruence and well-founded recursion -/

#check _root_.Array.foldlM_congr

@[congr] theorem mFoldlM_congr {f g : β → α → m β} {b : β} {xs xs' : Array α}
    {start start' stop stop' : Nat} (w : xs = xs') (h : ∀ x y, f x y = g x y)
    (hstart : start = start') (hstop : stop = stop') :
    xs.mFoldlM f b start stop = xs'.mFoldlM g b start' stop' := by
  subst w hstart hstop
  simp [funext fun x => funext (h x)]

#check _root_.Array.foldrM_congr

@[congr] theorem mFoldrM_congr {f g : α → β → m β} {b : β} {xs xs' : Array α}
    {start start' stop stop' : Nat} (w : xs = xs') (h : ∀ x y, f x y = g x y)
    (hstart : start = start') (hstop : stop = stop') :
    xs.mFoldrM f b start stop = xs'.mFoldrM g b start' stop' := by
  subst w hstart hstop
  simp [funext fun x => funext (h x)]

#check _root_.Array.forM_congr

@[congr] theorem mForM_congr {as bs : Array α} (w : as = bs) {f : α → m PUnit} :
    as.mForM f = bs.mForM f := by
  subst w
  rfl

#check _root_.Array.filterMapM_congr

@[congr] theorem mFilterMapM_congr {as bs : Array α} (w : as = bs)
    {f g : α → m (Option β)} (h : ∀ a, f a = g a) :
    as.mFilterMapM f = bs.mFilterMapM g := by
  subst w
  simp [mFilterMapM, h]

#check _root_.Array.flatMapM_congr

@[congr] theorem mFlatMapM_congr {as bs : Array α} (w : as = bs)
    {f g : α → m (Array β)} (h : ∀ a, f a = g a) :
    as.mFlatMapM f = bs.mFlatMapM g := by
  subst w
  simp [mFlatMapM, h]

#check _root_.Array.foldlM_attachWith

@[simp] theorem mFoldlM_attachWith {xs : Array α} {q : α → Prop}
    (H : ∀ a, a ∈ xs → q a) {f : β → {x // q x} → m β} {b : β} {stop : Nat}
    (w : stop = xs.size) :
    (xs.attachWith q H).mFoldlM f b 0 stop =
      xs.attach.mFoldlM (fun b ⟨a, h⟩ => f b ⟨a, H _ h⟩) b := by
  subst w
  rcases xs with ⟨xs⟩
  simp [List.mFoldlM_map]

#check _root_.Array.foldrM_attachWith

@[simp] theorem mFoldrM_attachWith {xs : Array α} {q : α → Prop}
    (H : ∀ a, a ∈ xs → q a) {f : {x // q x} → β → m β} {b : β} {start : Nat}
    (w : start = xs.size) :
    (xs.attachWith q H).mFoldrM f b start 0 =
      xs.attach.mFoldrM (fun a acc => f ⟨a.1, H _ a.2⟩ acc) b := by
  subst w
  rcases xs with ⟨xs⟩
  simp [List.mFoldrM_map]

#check _root_.Array.foldlM_subtype

@[simp] theorem mFoldlM_subtype {p : α → Prop} {xs : Array {x // p x}}
    {f : β → {x // p x} → m β} {g : β → α → m β} {x : β} {stop : Nat}
    (hf : ∀ b x h, f b ⟨x, h⟩ = g b x) (w : stop = xs.size) :
    xs.mFoldlM f x 0 stop = xs.unattach.mFoldlM g x 0 stop := by
  subst w
  rcases xs with ⟨xs⟩
  simp [List.mFoldlM_subtype hf]

#check _root_.Array.foldlM_wfParam

@[wf_preprocess] theorem mFoldlM_wfParam {xs : Array α} {f : β → α → m β} {init : β} :
    (wfParam xs).mFoldlM f init = xs.attach.unattach.mFoldlM f init := by
  simp [wfParam]

#check _root_.Array.foldlM_unattach

@[wf_preprocess] theorem mFoldlM_unattach {P : α → Prop} {xs : Array (Subtype P)}
    {f : β → α → m β} {init : β} :
    xs.unattach.mFoldlM f init = xs.mFoldlM (init := init) fun b ⟨x, h⟩ =>
      binderNameHint b f <| binderNameHint x (f b) <| binderNameHint h () <|
      f b (wfParam x) := by
  simp [wfParam]

#check _root_.Array.foldrM_subtype

@[simp] theorem mFoldrM_subtype {p : α → Prop} {xs : Array {x // p x}}
    {f : {x // p x} → β → m β} {g : α → β → m β} {x : β} {start : Nat}
    (hf : ∀ x h b, f ⟨x, h⟩ b = g x b) (w : start = xs.size) :
    xs.mFoldrM f x start 0 = xs.unattach.mFoldrM g x start 0 := by
  subst w
  rcases xs with ⟨xs⟩
  simp [List.mFoldrM_subtype hf]

#check _root_.Array.foldrM_wfParam

@[wf_preprocess] theorem mFoldrM_wfParam {xs : Array α} {f : α → β → m β} {init : β} :
    (wfParam xs).mFoldrM f init = xs.attach.unattach.mFoldrM f init := by
  simp [wfParam]

#check _root_.Array.foldrM_unattach

@[wf_preprocess] theorem mFoldrM_unattach {P : α → Prop} {xs : Array (Subtype P)}
    {f : α → β → m β} {init : β} :
    xs.unattach.mFoldrM f init = xs.mFoldrM (init := init) fun ⟨x, h⟩ b =>
      binderNameHint x f <| binderNameHint h () <| binderNameHint b (f x) <|
      f (wfParam x) b := by
  simp [wfParam]

#check _root_.Array.filterMapM_subtype

@[simp] theorem mFilterMapM_subtype {p : α → Prop} {xs : Array {x // p x}}
    {f : {x // p x} → m (Option β)} {g : α → m (Option β)} {stop : Nat}
    (hf : ∀ x h, f ⟨x, h⟩ = g x) (w : stop = xs.size) :
    xs.mFilterMapM f 0 stop = xs.unattach.mFilterMapM g := by
  subst w
  simp only [mFilterMapM, size_unattach]
  apply mFoldlM_subtype _ rfl
  simp [hf]

#check _root_.Array.filterMapM_wfParam

@[wf_preprocess] theorem mFilterMapM_wfParam {xs : Array α} {f : α → m (Option β)} :
    (wfParam xs).mFilterMapM f = xs.attach.unattach.mFilterMapM f := by
  simp [wfParam]

#check _root_.Array.filterMapM_unattach

@[wf_preprocess] theorem mFilterMapM_unattach {P : α → Prop} {xs : Array (Subtype P)}
    {f : α → m (Option β)} :
    xs.unattach.mFilterMapM f = xs.mFilterMapM fun ⟨x, h⟩ =>
      binderNameHint x f <| binderNameHint h () <| f (wfParam x) := by
  simp [wfParam]

#check _root_.Array.flatMapM_subtype

@[simp] theorem mFlatMapM_subtype {p : α → Prop} {xs : Array {x // p x}}
    {f : {x // p x} → m (Array β)} {g : α → m (Array β)} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    xs.mFlatMapM f = xs.unattach.mFlatMapM g := by
  simp only [mFlatMapM, size_unattach]
  apply mFoldlM_subtype _ rfl
  simp [hf]

#check _root_.Array.flatMapM_wfParam

@[wf_preprocess] theorem mFlatMapM_wfParam {xs : Array α} {f : α → m (Array β)} :
    (wfParam xs).mFlatMapM f = xs.attach.unattach.mFlatMapM f := by
  simp [wfParam]

#check _root_.Array.flatMapM_unattach

@[wf_preprocess] theorem mFlatMapM_unattach {P : α → Prop} {xs : Array (Subtype P)}
    {f : α → m (Array β)} :
    xs.unattach.mFlatMapM f = xs.mFlatMapM fun ⟨x, h⟩ =>
      binderNameHint x f <| binderNameHint h () <| f (wfParam x) := by
  simp [wfParam]

end Array

namespace Array

universe u v w
variable {α : Type u} {β : Type v} [MeasurableSpace β]
  {m : (γ : Type v) → [MeasurableSpace γ] → Type w} [MeasurableSpaceMonad m]

-- These compare the reference implementations directly, so recursion preprocessing
-- does not require monad laws or measurability hypotheses.
#check _root_.Array.mapM_subtype

@[simp] theorem mMapM_subtype {p : α → Prop} {xs : Array {x // p x}}
    {f : {x // p x} → m β} {g : α → m β} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    xs.mMapM f = xs.unattach.mMapM g := by
  simp only [mMapM, size_unattach]
  exact aux 0 _
where
  aux (i : Nat) (acc : Array β) :
      mMapM.map f xs i acc = mMapM.map g xs.unattach i acc := by
    unfold mMapM.map
    simp only [size_unattach]
    split
    · simp only [getElem_unattach, hf]
      apply MeasurableSpaceBind.bind_congr
      intro b
      exact aux (i + 1) (acc.push b)
    · rfl
  termination_by xs.size - i
  decreasing_by omega

#check _root_.Array.mapM_wfParam

@[wf_preprocess] theorem mMapM_wfParam {xs : Array α} {f : α → m β} :
    (wfParam xs).mMapM f = xs.attach.unattach.mMapM f := by
  simp [wfParam]

#check _root_.Array.mapM_unattach

@[wf_preprocess] theorem mMapM_unattach {P : α → Prop} {xs : Array (Subtype P)}
    {f : α → m β} :
    xs.unattach.mMapM f = xs.mMapM fun ⟨x, h⟩ =>
      binderNameHint x f <| binderNameHint h () <| f (wfParam x) := by
  simp [wfParam]

end Array

namespace List

universe u v w
variable {α : Type u} {β : Type v} [MeasurableSpace β]
  {m : (γ : Type v) → [MeasurableSpace γ] → Type w} [MeasurableSpaceMonad m]
  [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)] [LawfulMeasurableSpaceMonad m]

#check _root_.List.filterMapM_toArray'

@[simp] theorem mFilterMapM_toArray' {l : List α} {f : α → m (Option β)} {stop : Nat}
    (w : stop = l.length)
    (hf : ∀ a, Measurable (fun bs : List β =>
      (fun b => match b with | none => bs | some b => b :: bs) <$>ₘ f a)) :
    l.toArray.mFilterMapM f 0 stop = toArray <$>ₘ l.mFilterMapM f := by
  subst w
  exact mFilterMapM_toArray hf

end List

namespace Array

universe w
variable {α : Type} [MeasurableSpace α]
  {m : (γ : Type) → [MeasurableSpace γ] → Type w} [MeasurableSpaceMonad m]

#check _root_.Array.filterM_congr

@[congr] theorem mFilterM_congr {as bs : Array α} (w : as = bs)
    {p q : α → m Bool} (h : ∀ a, p a = q a) :
    as.mFilterM p = bs.mFilterM q := by
  subst w
  simp [mFilterM, h]

#check _root_.Array.filterRevM_congr

@[congr] theorem mFilterRevM_congr {as bs : Array α} (w : as = bs)
    {p q : α → m Bool} (h : ∀ a, p a = q a) :
    as.mFilterRevM p = bs.mFilterRevM q := by
  subst w
  simp [mFilterRevM, h]

variable [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)] [LawfulMeasurableSpaceMonad m]

#check _root_.List.filterM_toArray'

@[simp] theorem _root_.List.mFilterM_toArray' {l : List α} {p : α → m Bool} {stop : Nat}
    (w : stop = l.length)
    (hp : ∀ a, Measurable (fun bs : List α => (fun b => cond b (a :: bs) bs) <$>ₘ p a)) :
    l.toArray.mFilterM p 0 stop = List.toArray <$>ₘ l.mFilterM p := by
  subst w
  exact List.mFilterM_toArray hp

#check _root_.List.filterRevM_toArray'

@[simp] theorem _root_.List.mFilterRevM_toArray' {l : List α} {p : α → m Bool} {start : Nat}
    (w : start = l.length)
    (hp : ∀ a, Measurable (fun bs : List α => (fun b => cond b (a :: bs) bs) <$>ₘ p a)) :
    l.toArray.mFilterRevM p start 0 = List.toArray <$>ₘ l.mFilterRevM p := by
  subst w
  exact List.mFilterRevM_toArray hp

end Array
