/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.ForMathlib.MeasureTheory.MeasurableSpace.List
public import RandomDo.ForMathlib.MeasureTheory.MeasurableSpace.Option
public import RandomDo.MeasurableSpaceMonad.Instances.Id
public import RandomDo.RDo.Core

/-!
# Measurable space monadic list operations

This file defines monadic list operations for measurable space monads, including mapping,
filtering, folding, and searching, together with their laws and measurability lemmas.

## Main definitions

* `mMapM`: map a measurable space monadic function over a list.
* `mFilterM`: filter a list using a measurable space monadic predicate.
* `mFoldlM` and `mFoldrM`: fold a measurable space monadic function from left to right or right
  to left.
-/

@[expose] public section

open MeasureTheory

namespace List

universe u v w x

/-- Applies the measurable space monadic action `f` to every element in the list, left-to-right, and
returns the list of results. Analogue of core's `List.mapM`.

This implementation is tail recursive. `List.mMapM'` is a non-tail-recursive variant
that may be more convenient to reason about. -/
@[inline] def mMapM {m : (α : Type u) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] {α : Type w} {β : Type u} [MeasurableSpace β]
    (f : α → m β) (as : List α) : m (List β) :=
  let rec @[specialize, nolint docBlame] loop
    | [], bs => mPure bs.reverse
    | a :: as, bs => rdo loop as ((← f a) :: bs)
  loop as []

/-- Applies a measurable space monadic function to each element of the list along with the index at
which that element is found, returning the list of results. In addition to the index, the function
is also provided with a proof that the index is valid. Analogue of core's `List.mapFinIdxM`.

`List.mMapIdxM` is a variant that does not provide the function with evidence that the index is
valid. -/
@[inline] def mMapFinIdxM {m : (γ : Type u) → [MeasurableSpace γ] → Type v}
    [MeasurableSpaceMonad m]
    {α : Type w} {β : Type u} [MeasurableSpace β] (as : List α)
    (f : (i : Nat) → α → (h : i < as.length) → m β) : m (List β) :=
  go as #[] (by simp)
where
  @[specialize, nolint docBlame] go : (bs : List α) → (acc : Array β) →
      bs.length + acc.size = as.length → m (List β)
  | [], acc, h => mPure acc.toList
  | a :: as, acc, h => rdo
    go as (acc.push (← f acc.size a (by simp at h; omega))) (by simp at h ⊢; omega)

/-- Applies a monadic function to each element of the list along with the index at which that
element is found, returning the list of results. Analogue of core's `List.mapIdxM`.

`List.mMapFinIdxM` is a variant that additionally provides the function with a proof that the index
is valid. -/
@[inline] def mMapIdxM {m : (γ : Type u) → [MeasurableSpace γ] → Type v}
    [MeasurableSpaceMonad m]
    {α : Type w} {β : Type u} [MeasurableSpace β] (f : Nat → α → m β) (as : List α) : m (List β) :=
  go as #[]
where
  /-- Accumulator loop for `mMapIdxM`; the next index is `acc.size`. -/
  @[specialize, nolint docBlame] go : List α → Array β → m (List β)
  | [], acc => mPure acc.toList
  | a :: as, acc => rdo go as (acc.push (← f acc.size a))

/-- Applies the measurable space monadic action `f` to every element in the list, in order. Analogue
of core's `List.forM`. -/
@[specialize] protected def mForM {m : (α : Type u) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] {α : Type w} (as : List α) (f : α → m PUnit) : m PUnit :=
  match as with
  | [] => mPure ⟨⟩
  | a :: as => rdo f a; List.mForM as f

/-- Applies the measurable space monadic action `f` to the corresponding elements of two lists,
left-to-right, stopping at the end of the shorter list. `mZipWithM f as bs` is equivalent to
`mMapM id (zipWith f as bs)`. Analogue of core's `List.zipWithM`.

This implementation is tail recursive. `List.mZipWithM'` is a non-tail-recursive variant that may
be more convenient to reason about. -/
@[inline] def mZipWithM {m : (α : Type u) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] {α : Type w} {β : Type x} {γ : Type u} [MeasurableSpace γ]
    (f : α → β → m γ) (as : List α) (bs : List β) : m (List γ) :=
  let rec @[specialize, nolint docBlame] loop
    | a :: as, b :: bs, acc => rdo loop as bs (acc.push (← f a b))
    | _, _, acc => mPure acc.toList
  loop as bs #[]

/-- Helper function for `List.mFilterM`. Analogue of core's `List.filterAuxM`. -/
@[specialize] def mFilterAuxM {m : (α : Type) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] {α : Type} [MeasurableSpace α]
    (f : α → m Bool) : List α → List α → m (List α)
  | [], acc => mPure acc
  | a :: as, acc => rdo
    let b ← f a
    mFilterAuxM f as (cond b (a :: acc) acc)

/-- Applies the measurable space monadic predicate `p` to every element in the list, in order from
left to right, and returns the list of elements for which `p` returns `true`. Analogue of core's
`List.filterM`. -/
@[inline] def mFilterM {m : (α : Type) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] {α : Type} [MeasurableSpace α]
    (p : α → m Bool) (as : List α) : m (List α) := rdo
  let as ← mFilterAuxM p as []
  mPure as.reverse

/-- Applies the measurable space monadic predicate `p` to every element in the list in reverse
order, from right to left, and returns those elements for which `p` returns `true`. The elements of
the returned list are in the same order as in the input list. Analogue of core's `List.filterRevM`.
-/
@[inline] def mFilterRevM {m : (α : Type) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] {α : Type} [MeasurableSpace α]
    (p : α → m Bool) (as : List α) : m (List α) :=
  mFilterAuxM p as.reverse []

/-- Applies a measurable space monadic function that returns an `Option` to each element of a list,
collecting the non-`none` values. Analogue of core's `List.filterMapM`. -/
@[inline] def mFilterMapM {m : (α : Type u) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] {α : Type w} {β : Type u} [MeasurableSpace β]
    (f : α → m (Option β)) (as : List α) : m (List β) :=
  let rec @[specialize, nolint docBlame] loop
    | [], bs => mPure bs.reverse
    | a :: as, bs => rdo
      match (← f a) with
      | none => loop as bs
      | some b => loop as (b :: bs)
  loop as []

/-- Applies a measurable space monadic function that returns a list to each element of
a list, from left to right, and concatenates the resulting lists.
Analogue of core's `List.flatMapM`. -/
noncomputable def mFlatMapM {m : (α : Type u) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] {α : Type w} {β : Type u} [MeasurableSpace β]
    (f : α → m (List β)) (as : List α) : m (List β) :=
  let rec @[nolint docBlame] loop
    | [], bs => mPure bs.reverse.flatten
    | a :: as, bs => rdo
      let bs' ← f a
      loop as (bs' :: bs)
  loop as []

/-- Folds a measurable space monadic function over a list from the left, accumulating a value
starting with `init`. The accumulated value is combined with each element of the list in order,
using `f`. Analogue of core's `List.foldlM`. -/
@[specialize] def mFoldlM {m : (α : Type u) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] {s : Type u} [MeasurableSpace s] {α : Type w} :
    (f : s → α → m s) → (init : s) → List α → m s
  | _, s, [] => mPure s
  | f, s, a :: as => rdo
    let s' ← f s a
    List.mFoldlM f s' as

@[simp, grind =] theorem mFoldlM_nil
    {m : (α : Type u) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
    {α : Type w} {β : Type u} [MeasurableSpace β] {f : β → α → m β} {b : β} :
    [].mFoldlM f b = mPure b := rfl

@[simp, grind =] theorem mFoldlM_cons
    {m : (α : Type u) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
    {α : Type w} {β : Type u} [MeasurableSpace β] {f : β → α → m β}
    {b : β} {a : α} {l : List α} :
    (a :: l).mFoldlM f b = f b a >>=ₘ l.mFoldlM f := rfl

/-- Folds a measurable space monadic function over a list from the right, accumulating a value
starting with `init`. The accumulated value is combined with each element of the list in
reverse order, using `f`. Analogue of core's `List.foldrM`. -/
@[inline] def mFoldrM {m : (α : Type u) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] {s : Type u} [MeasurableSpace s] {α : Type w}
    (f : α → s → m s) (init : s) (l : List α) : m s :=
  List.mFoldlM (fun s a => f a s) init l.reverse

@[simp, grind =] theorem mFoldrM_nil
    {m : (α : Type u) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
    {α : Type w} {β : Type u} [MeasurableSpace β] {f : α → β → m β} {b : β} :
    [].mFoldrM f b = mPure b := rfl

/-- Returns true if the measurable space monadic predicate `p` returns `true` for any element of
`l`. Analogue of core's `List.anyM`. -/
@[specialize] def mAnyM {m : (α : Type) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] {α : Type w} (p : α → m Bool) : List α → m Bool
  | [] => mPure false
  | a :: as => rdo
    match (← p a) with
    | true => mPure true
    | false => mAnyM p as

/-- Returns true if the measurable space monadic predicate `p` returns `true` for every element of
`l`. Analogue of core's `List.allM`. -/
@[specialize] def mAllM {m : (α : Type) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] {α : Type w} (p : α → m Bool) : List α → m Bool
  | [] => mPure true
  | a :: as => rdo
    match (← p a) with
    | true => mAllM p as
    | false => mPure false

/-- Returns the first element of the list for which the measurable space monadic predicate `p`
returns `true`, or `none` if no such element is found. Elements of the list are checked in order.
Analogue of core's `List.findM?`. -/
@[specialize] def mFindM? {m : (α : Type) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] {α : Type} [MeasurableSpace α]
    (p : α → m Bool) : List α → m (Option α)
  | [] => mPure none
  | a :: as => rdo
    match (← p a) with
    | true => mPure (some a)
    | false => mFindM? p as

/-- Returns the first non-`none` result of applying the measurable space monadic function `f` to
each element of the list, in order. Returns `none` if `f` returns `none` for all elements.
Analogue of core's `List.findSomeM?`. -/
@[specialize] def mFindSomeM? {m : (α : Type u) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] {α : Type w} {β : Type u} [MeasurableSpace β]
    (f : α → m (Option β)) : List α → m (Option β)
  | [] => mPure none
  | a :: as => rdo
    match (← f a) with
    | some b => mPure (some b)
    | none => mFindSomeM? f as

variable {m : (α : Type u) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
  {α : Type w} {β : Type u} [MeasurableSpace β]

section

variable [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)] [LawfulMeasurableSpaceMonad m]

section Measurability

@[fun_prop] theorem measurable_mFoldlM (l : List α) {f : β → α → m β}
    (hf : ∀ a, Measurable (fun b => f b a)) :
    Measurable (fun init => l.mFoldlM f init) := by
  induction l <;> simp only [mFoldlM_nil, mFoldlM_cons] <;> fun_prop

@[fun_prop] theorem measurable_mFoldrM (l : List α) {f : α → β → m β}
    (hf : ∀ a, Measurable (f a)) : Measurable (fun init => l.mFoldrM f init) :=
  measurable_mFoldlM l.reverse hf

@[fun_prop] theorem measurable_mMapM_loop (l : List α) {f : α → m β}
    (hf : ∀ a, Measurable (fun bs => (fun b => b :: bs) <$>ₘ f a)) :
    Measurable (mMapM.loop f l) := by
  induction l with
  | nil => simp only [mMapM.loop]; fun_prop
  | cons a l ih =>
    simpa (disch := fun_prop) [Function.comp_def, mMapM.loop] using
      (measurable_mBind ih).comp (hf a)

@[fun_prop] theorem measurable_mZipWithM_loop {α' : Type x} (as : List α) (bs : List α')
    {f : α → α' → m β}
    (hf : ∀ a b, Measurable (fun acc : Array β => (fun c => acc.push c) <$>ₘ f a b)) :
    Measurable (mZipWithM.loop f as bs) := by
  induction as generalizing bs with
  | nil => simp only [mZipWithM.loop]; fun_prop
  | cons a as ih =>
    cases bs with
    | nil => simp only [mZipWithM.loop]; fun_prop
    | cons b bs =>
      simpa (disch := fun_prop) [Function.comp_def, mZipWithM.loop] using
        (measurable_mBind (ih bs)).comp (hf a b)

@[fun_prop] theorem measurable_mFilterMapM_loop (l : List α) {f : α → m (Option β)}
    (hf : ∀ a, Measurable (fun bs =>
      (fun b => match b with | none => bs | some b => b :: bs) <$>ₘ f a)) :
    Measurable (mFilterMapM.loop f l) := by
  induction l with
  | nil => simp only [mFilterMapM.loop]; fun_prop
  | cons a l ih =>
    refine ((measurable_mBind ih).comp (hf a)).congr fun bs => ?_
    simp (disch := fun_prop) only [Function.comp_apply, mFilterMapM.loop, mBind_mMap_left]
    exact MeasurableSpaceBind.bind_congr fun b => by cases b <;> rfl

@[fun_prop] theorem measurable_mFlatMapM_loop (l : List α) {f : α → m (List β)}
    (hf : ∀ a, Measurable (fun bs => (fun b => b :: bs) <$>ₘ f a)) :
    Measurable (mFlatMapM.loop f l) := by
  induction l with
  | nil => simp only [mFlatMapM.loop]; fun_prop
  | cons a l ih =>
    simpa (disch := fun_prop) [Function.comp_def, mFlatMapM.loop] using
      (measurable_mBind ih).comp (hf a)

@[fun_prop] theorem measurable_mFilterAuxM
    {m : (γ : Type) → [MeasurableSpace γ] → Type v} [MeasurableSpaceMonad m]
    [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)] [LawfulMeasurableSpaceMonad m]
    {α : Type} [MeasurableSpace α] (l : List α) {f : α → m Bool}
    (hf : ∀ a, Measurable (fun bs =>
      (fun b => cond b (a :: bs) bs) <$>ₘ f a)) : Measurable (mFilterAuxM f l) := by
  induction l with
  | nil => simp only [mFilterAuxM]; fun_prop
  | cons a l ih =>
    simpa (disch := fun_prop) [Function.comp_def, mFilterAuxM] using
      (measurable_mBind ih).comp (hf a)

end Measurability

@[simp] theorem mFoldlM_append {f : β → α → m β} {b : β} {l l' : List α}
    (hf : ∀ a, Measurable (fun b => f b a)) :
    (l ++ l').mFoldlM f b = l.mFoldlM f b >>=ₘ l'.mFoldlM f := by
  induction l generalizing b <;> simp (disch := fun_prop) [*]

@[simp, grind =] theorem mFoldrM_cons {a : α} {l : List α} {f : α → β → m β} {b : β}
    (hf : ∀ a, Measurable (f a)) :
    (a :: l).mFoldrM f b = l.mFoldrM f b >>=ₘ f a := by
  simp (disch := fun_prop) [mFoldrM]

@[simp] theorem mFoldlM_pure {f : β → α → β} {b : β} {l : List α}
    (hf : ∀ a, Measurable (fun b => f b a)) :
    l.mFoldlM (m := m) (mPure <| f · ·) b = mPure (l.foldl f b) := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    rw [mFoldlM_cons, mPure_mBind _ (by fun_prop), ih]
    rfl

@[simp] theorem mFoldrM_pure {f : α → β → β} {b : β} {l : List α}
    (hf : ∀ a, Measurable (f a)) :
    l.mFoldrM (m := m) (mPure <| f · ·) b = mPure (l.foldr f b) := by
  induction l generalizing b <;> simp (disch := fun_prop) [*]

end

theorem foldl_eq_mFoldlM {f : β → α → β} {b : β} {l : List α} :
    l.foldl f b = (l.mFoldlM (m := MId) (mPure <| f · ·) b).run := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => exact ih

theorem foldr_eq_mFoldrM {f : α → β → β} {b : β} {l : List α} :
    l.foldr f b = (l.mFoldrM (m := MId) (mPure <| f · ·) b).run := by
  rw [mFoldrM, ← foldl_eq_mFoldlM, _root_.List.foldl_reverse]

theorem idRun_mFoldlM {f : β → α → Id β} {b : β} {l : List α} :
    Id.run (l.mFoldlM (m := MId) f b) = l.foldl (f · · |>.run) b :=
  foldl_eq_mFoldlM.symm

theorem idRun_mFoldrM {f : α → β → Id β} {b : β} {l : List α} :
    Id.run (l.mFoldrM (m := MId) f b) = l.foldr (f · · |>.run) b :=
  foldr_eq_mFoldrM.symm

@[simp] theorem mFoldlM_reverse {l : List α} {f : β → α → m β} {b : β} :
    l.reverse.mFoldlM f b = l.mFoldrM (fun x y => f y x) b := rfl

@[simp] theorem mFoldrM_reverse {l : List α} {f : α → β → m β} {b : β} :
    l.reverse.mFoldrM f b = l.mFoldlM (fun x y => f y x) b := by
  simp [mFoldrM]

@[simp] theorem mFoldrM_append
    [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)] [LawfulMeasurableSpaceMonad m]
    {f : α → β → m β} {b : β} {l l' : List α} (hf : ∀ a, Measurable (f a)) :
    (l ++ l').mFoldrM f b = l'.mFoldrM f b >>=ₘ l.mFoldrM f := by
  induction l <;> simp (disch := fun_prop) [*]

@[simp, grind =] theorem mForM_nil {f : α → m PUnit} :
    List.mForM [] f = mPure ⟨⟩ := rfl

@[simp, grind =] theorem mForM_cons {f : α → m PUnit} {a : α} {as : List α} :
    List.mForM (a :: as) f = f a >>=ₘ fun _ => List.mForM as f := rfl

@[simp] theorem mFindM?_pure
    {m : (α : Type) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
    [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)] [LawfulMeasurableSpaceMonad m]
    {α : Type} [MeasurableSpace α] (p : α → Bool) (as : List α) :
    mFindM? (m := m) (mPure <| p ·) as = mPure (as.find? p) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    cases h : p a <;> simp (disch := fun_prop) [mFindM?, find?_cons, h, ih]

@[simp, grind =] theorem idRun_mFindM? {α : Type} [MeasurableSpace α]
    (p : α → Id Bool) (as : List α) :
    (mFindM? (m := MId) p as).run = as.find? (p · |>.run) :=
  mFindM?_pure _ _

@[simp, grind =] theorem mFindSomeM?_nil {f : α → m (Option β)} :
    [].mFindSomeM? f = mPure none := rfl

@[grind =] theorem mFindSomeM?_cons {f : α → m (Option β)} {a : α} {as : List α} :
    (a :: as).mFindSomeM? f = (rdo
      match ← f a with
      | some b => return some b
      | none => as.mFindSomeM? f) := rfl

@[simp] theorem mFindSomeM?_pure
    [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)] [LawfulMeasurableSpaceMonad m]
    {f : α → Option β} {as : List α} :
    mFindSomeM? (m := m) (mPure <| f ·) as = mPure (as.findSome? f) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    cases h : f a <;> simp (disch := fun_prop) [mFindSomeM?, findSome?, h, ih]

@[simp, grind =] theorem idRun_mFindSomeM? (f : α → Id (Option β)) (as : List α) :
    (mFindSomeM? (m := MId) f as).run = as.findSome? (f · |>.run) :=
  mFindSomeM?_pure

theorem findSome?_eq_mFindSomeM? {f : α → Option β} {as : List α} :
    as.findSome? f =
      (as.mFindSomeM? (m := MId) (mPure <| f ·)).run :=
  (idRun_mFindSomeM? _ _).symm

theorem mFindM?_eq_mFindSomeM?
    {m : (α : Type) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]
    [∀ γ, [MeasurableSpace γ] → MeasurableSpace (m γ)] [LawfulMeasurableSpaceMonad m]
    {α : Type} [MeasurableSpace α] {p : α → m Bool} {as : List α} :
    as.mFindM? p = as.mFindSomeM? fun a => rdo return if (← p a) then some a else none := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp (disch := fun_prop) only [mFindM?, mFindSomeM?, mBind_assoc]
    apply MeasurableSpaceBind.bind_congr
    intro b
    cases b <;> simp (disch := fun_prop) [ih]

attribute [simp] mFilterAuxM mAnyM mAllM mFindM? mFindSomeM?

/-- Applies the measurable space monadic action `f` on every element in the list, left-to-right,
and returns the list of results. Analogue of core's `List.mapM'`.

This is a non-tail-recursive variant of `List.mMapM` that's easier to reason about. -/
def mMapM' (f : α → m β) : List α → m (List β)
  | [] => mPure []
  | a :: l => rdo return (← f a) :: (← mMapM' f l)

@[simp] theorem mMapM'_nil {f : α → m β} : mMapM' f [] = mPure [] := rfl

@[simp] theorem mMapM'_cons {f : α → m β} {a : α} {l : List α} :
    mMapM' f (a :: l) = (rdo return (← f a) :: (← l.mMapM' f)) := rfl

section

variable [∀ δ, [MeasurableSpace δ] → MeasurableSpace (m δ)] [LawfulMeasurableSpaceMonad m]

theorem mMapM_loop_eq {f : α → m β} (l : List α) (acc : List β)
    (hf : ∀ a, Measurable (fun bs => (fun b => b :: bs) <$>ₘ f a)) :
    mMapM.loop f l acc = (acc.reverse ++ ·) <$>ₘ mMapM' f l := by
  induction l generalizing acc with
  | nil => simp (disch := fun_prop) [mMapM.loop, mMapM']
  | cons a l ih =>
    have hcons : Measurable (fun b => (fun bs => b :: bs) <$>ₘ mMapM' f l) := by
      simpa [Function.comp_def, ih] using (measurable_mMapM_loop l hf).comp
        (show Measurable (fun b : β => [b]) by fun_prop)
    simp (disch := fun_prop) [mMapM.loop, mMapM', ih, mMap_mBind, mMap_mMap]

theorem mMapM'_eq_mMapM {f : α → m β} {l : List α}
    (hf : ∀ a, Measurable (fun bs => (fun b => b :: bs) <$>ₘ f a)) :
    mMapM' f l = mMapM f l := by
  simp [mMapM, mMapM_loop_eq _ _ hf]

@[fun_prop] theorem measurable_append_mMapM (l : List α) {f : α → m β}
    (hf : ∀ a, Measurable (fun bs => (fun b => b :: bs) <$>ₘ f a)) :
    Measurable (fun bs => (bs ++ ·) <$>ₘ l.mMapM f) := by
  simpa [Function.comp_def, mMapM_loop_eq _ _ hf, mMapM'_eq_mMapM hf] using
    (measurable_mMapM_loop l hf).comp measurable_list_reverse

@[fun_prop] theorem measurable_cons_mMapM (l : List α) {f : α → m β}
    (hf : ∀ a, Measurable (fun bs => (fun b => b :: bs) <$>ₘ f a)) :
    Measurable (fun b => (fun bs => b :: bs) <$>ₘ l.mMapM f) := by
  simpa [Function.comp_def] using (measurable_append_mMapM l hf).comp
    (show Measurable (fun b : β => [b]) by fun_prop)

end

@[simp, grind =] theorem mMapM_nil {f : α → m β} : [].mMapM f = mPure [] := rfl

section

variable [∀ δ, [MeasurableSpace δ] → MeasurableSpace (m δ)] [LawfulMeasurableSpaceMonad m]

@[simp, grind =] theorem mMapM_cons {f : α → m β} {a : α} {l : List α}
    (hf : ∀ a, Measurable (fun bs => (fun b => b :: bs) <$>ₘ f a)) :
    (a :: l).mMapM f = (rdo return (← f a) :: (← l.mMapM f)) := by
  simp [← mMapM'_eq_mMapM hf]

@[simp] theorem mMapM_pure
    {l : List α} {f : α → β} : l.mMapM (m := m) (mPure <| f ·) = mPure (l.map f) := by
  suffices h : ∀ l acc, mMapM.loop (m := m) (mPure <| f ·) l acc =
      mPure (acc.reverse ++ l.map f) from h l []
  intro l acc
  induction l generalizing acc <;> simp (disch := fun_prop) [mMapM.loop, *]

end

@[simp, grind =] theorem idRun_mMapM {l : List α} {f : α → Id β} :
    (l.mMapM (m := MId) f).run = l.map (f · |>.run) :=
  mMapM_pure

@[simp, grind =] theorem mMapM_map {α' : Type x} {f : α → α'} {g : α' → m β} {l : List α} :
    (l.map f).mMapM g = l.mMapM (g ∘ f) := by
  suffices h : ∀ l acc, mMapM.loop g (l.map f) acc = mMapM.loop (g ∘ f) l acc from h l []
  intro l acc
  induction l generalizing acc <;> simp [mMapM.loop, *]

section

variable [∀ δ, [MeasurableSpace δ] → MeasurableSpace (m δ)] [LawfulMeasurableSpaceMonad m]

@[simp, grind =] theorem mMapM_append {f : α → m β} {l₁ l₂ : List α}
    (hf : ∀ a, Measurable (fun bs => (fun b => b :: bs) <$>ₘ f a)) :
    (l₁ ++ l₂).mMapM f = (rdo return (← l₁.mMapM f) ++ (← l₂.mMapM f)) := by
  induction l₁ with
  | nil => simp (disch := fun_prop)
  | cons a l₁ ih =>
    simp (disch := fun_prop) [mMapM_cons hf, ih, mMap_mBind, mBind_mMap_left, mMap_mMap]

theorem mFoldlM_cons_eq_append {f : α → m β} {as : List α} {b : β} {bs : List β}
    (hf : ∀ a, Measurable (fun bs => (fun b => b :: bs) <$>ₘ f a)) :
    (as.mFoldlM (init := b :: bs) fun acc a => (· :: acc) <$>ₘ f a) =
      (· ++ b :: bs) <$>ₘ as.mFoldlM (init := []) fun acc a => (· :: acc) <$>ₘ f a := by
  induction as generalizing b bs with
  | nil => simp (disch := fun_prop)
  | cons a as ih =>
    simp (disch := fun_prop) only [mFoldlM_cons, mMap_mBind, mBind_mMap_left]
    simp (disch := fun_prop) [ih]

theorem mMapM_eq_reverse_mFoldlM_cons {f : α → m β} {l : List α}
    (hf : ∀ a, Measurable (fun bs => (fun b => b :: bs) <$>ₘ f a)) :
    mMapM f l = reverse <$>ₘ (l.mFoldlM (fun acc a => (· :: acc) <$>ₘ f a) []) := by
  rw [← mMapM'_eq_mMapM hf]
  induction l with
  | nil => simp (disch := fun_prop)
  | cons a as ih =>
    simp (disch := fun_prop) only [mMapM'_cons, mFoldlM_cons, mBind_mMap_left, mMap_mBind]
    simp (disch := fun_prop) [ih, mFoldlM_cons_eq_append hf]

end

@[simp, grind =] theorem mFilterMapM_nil {f : α → m (Option β)} :
    [].mFilterMapM f = mPure [] := rfl

section

variable [∀ δ, [MeasurableSpace δ] → MeasurableSpace (m δ)] [LawfulMeasurableSpaceMonad m]

theorem mFilterMapM_loop_eq {f : α → m (Option β)} {l : List α} {acc : List β}
    (hf : ∀ a, Measurable (fun bs =>
      (fun b => match b with | none => bs | some b => b :: bs) <$>ₘ f a)) :
    mFilterMapM.loop f l acc = (acc.reverse ++ ·) <$>ₘ mFilterMapM.loop f l [] := by
  induction l generalizing acc with
  | nil => simp (disch := fun_prop) [mFilterMapM.loop]
  | cons a l ih =>
    simp only [mFilterMapM.loop]
    rw [mMap_mBind (f := fun xs => acc.reverse ++ xs) (by fun_prop) (f a)]
    · apply MeasurableSpaceBind.bind_congr
      intro b
      cases b with
      | none => exact ih
      | some b =>
        dsimp only
        rw [ih, ih (acc := [b])]
        simp (disch := fun_prop)
    · fun_prop

@[simp, grind =] theorem mFilterMapM_cons {f : α → m (Option β)} {a : α} {l : List α}
    (hf : ∀ a, Measurable (fun bs =>
      (fun b => match b with | none => bs | some b => b :: bs) <$>ₘ f a)) :
    (a :: l).mFilterMapM f = (rdo
      match ← f a with
      | none => mFilterMapM f l
      | some b => return b :: (← mFilterMapM f l)) := by
  simp only [mFilterMapM, mFilterMapM.loop]
  apply MeasurableSpaceBind.bind_congr
  intro b
  cases b with
  | none => rfl
  | some b =>
    simpa (disch := fun_prop) using (mFilterMapM_loop_eq (acc := [b]) hf)

end

/--
Applies the measurable space monadic action `f` to the corresponding elements of two lists,
left-to-right, stopping at the end of the shorter list. `mZipWithM' f as bs` is equivalent to
`mMapM id (zipWith f as bs)` for lawful `MeasurableSpaceMonad` instances with measurable accumulator
updates. Analogue of core's `List.zipWithM'`.
-/
def mZipWithM' {α' : Type x} (f : α → α' → m β) : List α → List α' → m (List β)
  | x :: xs, y :: ys => rdo
    let z ← f x y
    let zs ← mZipWithM' f xs ys
    return z :: zs
  | _, _ => mPure []

@[simp, grind =] theorem mZipWithM'_nil_left {α' : Type x} {f : α → α' → m β} {l} :
    mZipWithM' f [] l = mPure [] := rfl

@[simp, grind =] theorem mZipWithM'_nil_right {α' : Type x} {f : α → α' → m β} {l} :
    mZipWithM' f l [] = mPure [] := by simp [mZipWithM']

@[simp, grind =] theorem mZipWithM'_cons_cons {α' : Type x} {f : α → α' → m β}
    {a : α} {as : List α} {b : α'} {bs : List α'} :
    mZipWithM' f (a :: as) (b :: bs) =
      (rdo return (← f a b) :: (← mZipWithM' f as bs)) := rfl

section

variable [∀ δ, [MeasurableSpace δ] → MeasurableSpace (m δ)] [LawfulMeasurableSpaceMonad m]

theorem mZipWithM_loop_eq
    {α' : Type x} {f : α → α' → m β} (as : List α) (bs : List α') (acc : Array β)
    (hf : ∀ a b, Measurable (fun acc : Array β => (fun c => acc.push c) <$>ₘ f a b)) :
    mZipWithM.loop f as bs acc = (acc.toList ++ ·) <$>ₘ mZipWithM' f as bs := by
  induction as generalizing bs acc with
  | nil => simp (disch := fun_prop) [mZipWithM.loop]
  | cons a as ih =>
    cases bs with
    | nil => simp (disch := fun_prop) [mZipWithM.loop]
    | cons b bs =>
      have hcons : Measurable (fun c => (fun cs => c :: cs) <$>ₘ mZipWithM' f as bs) := by
        simpa [Function.comp_def, ih] using (measurable_mZipWithM_loop as bs hf).comp
          (show Measurable (fun c : β => #[c]) by fun_prop)
      simp (disch := fun_prop) [mZipWithM.loop, mZipWithM', ih, mMap_mBind, mMap_mMap]

@[grind =] theorem mZipWithM'_eq_mZipWithM
    {α' : Type x} {f : α → α' → m β} {l : List α} {l' : List α'}
    (hf : ∀ a b, Measurable (fun acc : Array β => (fun c => acc.push c) <$>ₘ f a b)) :
    mZipWithM' f l l' = mZipWithM f l l' := by
  simp [mZipWithM, mZipWithM_loop_eq _ _ _ hf]

end

@[simp, grind =] theorem mZipWithM_nil_left {α' : Type x} {f : α → α' → m β} {l} :
    mZipWithM f [] l = mPure [] := rfl

@[simp, grind =] theorem mZipWithM_nil_right {α' : Type x} {f : α → α' → m β} {l} :
    mZipWithM f l [] = mPure [] := by simp [mZipWithM, mZipWithM.loop]

section

variable [∀ δ, [MeasurableSpace δ] → MeasurableSpace (m δ)] [LawfulMeasurableSpaceMonad m]

@[simp, grind =] theorem mZipWithM_cons_cons
    {α' : Type x} {f : α → α' → m β} {a : α} {as : List α} {b : α'} {bs : List α'}
    (hf : ∀ a b, Measurable (fun acc : Array β => (fun c => acc.push c) <$>ₘ f a b)) :
    mZipWithM f (a :: as) (b :: bs) = (rdo return (← f a b) :: (← mZipWithM f as bs)) := by
  simp [← mZipWithM'_eq_mZipWithM hf]

@[simp, grind =] theorem mZipWithM'_eq_mMapM_id_zipWith
    {α' : Type x} {f : α → α' → m β} {as : List α} {bs : List α'}
    (hf : ∀ a b, Measurable (fun acc : Array β => (fun c => acc.push c) <$>ₘ f a b)) :
    mZipWithM' f as bs = mMapM id (zipWith f as bs) := by
  rw [mZipWithM'_eq_mZipWithM hf]
  suffices h : ∀ as bs acc, mZipWithM.loop f as bs acc =
      mMapM.loop id (zipWith f as bs) acc.toList.reverse from h as bs #[]
  intro as bs acc
  induction as generalizing bs acc <;> cases bs <;>
    simp [mZipWithM.loop, mMapM.loop, zipWith, *]

end

@[simp, grind =] theorem mFlatMapM_nil {f : α → m (List β)} : [].mFlatMapM f = mPure [] := rfl

section

variable [∀ δ, [MeasurableSpace δ] → MeasurableSpace (m δ)] [LawfulMeasurableSpaceMonad m]

theorem mFlatMapM_loop_eq {f : α → m (List β)} {l : List α} {acc : List (List β)}
    (hf : ∀ a, Measurable (fun bs => (fun b => b :: bs) <$>ₘ f a)) :
    mFlatMapM.loop f l acc = (acc.reverse.flatten ++ ·) <$>ₘ mFlatMapM.loop f l [] := by
  induction l generalizing acc with
  | nil => simp (disch := fun_prop) [mFlatMapM.loop]
  | cons a l ih =>
    simp (disch := fun_prop) only [mFlatMapM.loop, mMap_mBind]
    apply MeasurableSpaceBind.bind_congr
    intro bs
    rw [ih, ih (acc := [bs])]
    simp (disch := fun_prop)

@[simp, grind =] theorem mFlatMapM_cons {f : α → m (List β)} {a : α} {l : List α}
    (hf : ∀ a, Measurable (fun bs => (fun b => b :: bs) <$>ₘ f a)) :
    (a :: l).mFlatMapM f = (rdo
      let bs ← f a
      return bs ++ (← l.mFlatMapM f)) := by
  simp only [mFlatMapM, mFlatMapM.loop]
  apply MeasurableSpaceBind.bind_congr
  intro bs
  rw [mFlatMapM_loop_eq hf]
  simp (disch := fun_prop)

end

theorem mFoldlM_map {α' : Type x} {f : α → α'} {g : β → α' → m β}
    {l : List α} {init : β} :
    (l.map f).mFoldlM g init = l.mFoldlM (fun x y => g x (f y)) init := by
  induction l generalizing g init <;> simp [*]

theorem mFoldrM_map {α' : Type x} {f : α → α'} {g : α' → β → m β}
    {l : List α} {init : β} :
    (l.map f).mFoldrM g init = l.mFoldrM (fun x y => g (f x) y) init := by
  rw [mFoldrM, ← map_reverse, mFoldlM_map, mFoldrM]

section

variable [∀ δ, [MeasurableSpace δ] → MeasurableSpace (m δ)] [LawfulMeasurableSpaceMonad m]

theorem mFoldlM_filterMap
    {α' : Type x} {f : α → Option α'} {g : β → α' → m β} {l : List α} {init : β}
    (hg : ∀ a, Measurable (fun b => g b a)) :
    (l.filterMap f).mFoldlM g init =
      l.mFoldlM (fun x y => match f y with | some b => g x b | none => mPure x) init := by
  have hstep : ∀ a, Measurable (fun x =>
      match f a with | some b => g x b | none => mPure x) := by
    intro a
    cases f a <;> fun_prop
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    simp only [filterMap_cons, mFoldlM_cons]
    cases f a <;> simp (disch := fun_prop) [ih]

theorem mFoldrM_filterMap
    {α' : Type x} {f : α → Option α'} {g : α' → β → m β} {l : List α} {init : β}
    (hg : ∀ a, Measurable (g a)) :
    (l.filterMap f).mFoldrM g init =
      l.mFoldrM (fun x y => match f x with | some b => g b y | none => mPure y) init := by
  rw [mFoldrM, ← filterMap_reverse, mFoldlM_filterMap hg, mFoldrM]

theorem mFoldlM_filter {p : α → Bool} {g : β → α → m β} {l : List α} {init : β}
    (hg : ∀ a, Measurable (fun b => g b a)) :
    (l.filter p).mFoldlM g init =
      l.mFoldlM (fun x y => if p y then g x y else mPure x) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    simp only [filter_cons, mFoldlM_cons]
    split <;> simp (disch := fun_prop) [ih]

theorem mFoldrM_filter {p : α → Bool} {g : α → β → m β} {l : List α} {init : β}
    (hg : ∀ a, Measurable (g a)) :
    (l.filter p).mFoldrM g init =
      l.mFoldrM (fun x y => if p x then g x y else mPure y) init := by
  rw [mFoldrM, ← filter_reverse, mFoldlM_filter hg, mFoldrM]

end

@[simp] theorem mFoldlM_attachWith
    {l : List α} {q : α → Prop} (H : ∀ a, a ∈ l → q a)
    {f : β → {x // q x} → m β} {b : β} :
    (l.attachWith q H).mFoldlM f b =
      l.attach.mFoldlM (fun b ⟨a, h⟩ => f b ⟨a, H _ h⟩) b := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [ih, mFoldlM_map]

@[simp] theorem mFoldrM_attachWith
    {l : List α} {q : α → Prop} (H : ∀ a, a ∈ l → q a)
    {f : {x // q x} → β → m β} {b : β} :
    (l.attachWith q H).mFoldrM f b =
      l.attach.mFoldrM (fun a acc => f ⟨a.1, H _ a.2⟩ acc) b := by
  simp only [mFoldrM, reverse_attachWith, reverse_attach, mFoldlM_map]
  exact mFoldlM_attachWith _

@[simp, grind =] theorem mForM_append
    [∀ δ, [MeasurableSpace δ] → MeasurableSpace (m δ)] [LawfulMeasurableSpaceMonad m]
    {l₁ l₂ : List α} {f : α → m PUnit} :
    List.mForM (l₁ ++ l₂) f = (rdo List.mForM l₁ f; List.mForM l₂ f) := by
  induction l₁ <;> simp (disch := fun_prop) [*]

@[simp, grind =] theorem mForM_map {α' : Type x}
    {l : List α} {g : α → α'} {f : α' → m PUnit} :
    List.mForM (l.map g) f = List.mForM l (fun a => f (g a)) := by
  induction l <;> simp [*]

section

variable {m : (α : Type) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]

theorem mAllM_eq_not_mAnyM_not
    [∀ δ, [MeasurableSpace δ] → MeasurableSpace (m δ)] [LawfulMeasurableSpaceMonad m]
    {p : α → m Bool} {as : List α} :
    mAllM p as = (! ·) <$>ₘ mAnyM ((! ·) <$>ₘ p ·) as := by
  induction as with
  | nil => simp (disch := fun_prop)
  | cons a as ih =>
    simp (disch := fun_prop) only [mAllM, mAnyM, mBind_mMap_left, mMap_mBind]
    apply MeasurableSpaceBind.bind_congr
    intro b
    cases b <;> simp (disch := fun_prop) [ih]

@[simp] theorem mAnyM_pure
    [∀ δ, [MeasurableSpace δ] → MeasurableSpace (m δ)] [LawfulMeasurableSpaceMonad m]
    {p : α → Bool} {as : List α} :
    as.mAnyM (m := m) (mPure <| p ·) = mPure (as.any p) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    cases h : p a <;> simp (disch := fun_prop) [h, ih]

@[simp] theorem mAnyM_nil {p : α → m Bool} : [].mAnyM p = mPure false := rfl

theorem mAnyM_cons {p : α → m Bool} {x : α} {xs : List α} :
    (x :: xs).mAnyM p = (rdo
      if ← p x then return true else xs.mAnyM p) := by
  rw [mAnyM]
  apply MeasurableSpaceBind.bind_congr
  intro px
  cases px <;> rfl

@[simp] theorem mAllM_pure
    [∀ δ, [MeasurableSpace δ] → MeasurableSpace (m δ)] [LawfulMeasurableSpaceMonad m]
    {p : α → Bool} {as : List α} :
    as.mAllM (m := m) (mPure <| p ·) = mPure (as.all p) := by
  simp (disch := fun_prop) [mAllM_eq_not_mAnyM_not, all_eq_not_any_not]

@[simp] theorem mAllM_nil {p : α → m Bool} : [].mAllM p = mPure true := rfl

theorem mAllM_cons {p : α → m Bool} {x : α} {xs : List α} :
    (x :: xs).mAllM p = (rdo
      if ← p x then xs.mAllM p else return false) := by
  rw [mAllM]
  apply MeasurableSpaceBind.bind_congr
  intro px
  cases px <;> rfl

end

@[simp] theorem mFoldlM_subtype {p : α → Prop} {l : List {x // p x}}
    {f : β → {x // p x} → m β} {g : β → α → m β} {x : β}
    (hf : ∀ b x h, f b ⟨x, h⟩ = g b x) :
    l.mFoldlM f x = l.unattach.mFoldlM g x := by
  induction l generalizing x <;> simp [*]

@[wf_preprocess] theorem mFoldlM_wfParam {xs : List α} {f : β → α → m β} {init : β} :
    (wfParam xs).mFoldlM f init = xs.attach.unattach.mFoldlM f init := by
  simp [wfParam]

@[wf_preprocess] theorem mFoldlM_unattach
    {P : α → Prop} {xs : List (Subtype P)} {f : β → α → m β} {init : β} :
    xs.unattach.mFoldlM f init = xs.mFoldlM (init := init) fun b ⟨x, h⟩ =>
      binderNameHint b f <| binderNameHint x (f b) <| binderNameHint h () <|
      f b (wfParam x) := by
  simp [wfParam]

@[simp] theorem mFoldrM_subtype {p : α → Prop} {l : List {x // p x}}
    {f : {x // p x} → β → m β} {g : α → β → m β} {x : β}
    (hf : ∀ x h b, f ⟨x, h⟩ b = g x b) :
    l.mFoldrM f x = l.unattach.mFoldrM g x := by
  rw [mFoldrM, mFoldlM_subtype (fun b x h => hf x h b), unattach_reverse, mFoldrM]

@[wf_preprocess] theorem mFoldrM_wfParam {xs : List α} {f : α → β → m β} {init : β} :
    (wfParam xs).mFoldrM f init = xs.attach.unattach.mFoldrM f init := by
  simp [wfParam]

@[wf_preprocess] theorem mFoldrM_unattach
    {P : α → Prop} {xs : List (Subtype P)} {f : α → β → m β} {init : β} :
    xs.unattach.mFoldrM f init = xs.mFoldrM (init := init) fun ⟨x, h⟩ b =>
      binderNameHint x f <| binderNameHint h () <| binderNameHint b (f x) <|
      f (wfParam x) b := by
  simp [wfParam]

@[simp] theorem mMapM_subtype {p : α → Prop} {l : List {x // p x}}
    {f : {x // p x} → m β} {g : α → m β} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    l.mMapM f = l.unattach.mMapM g := by
  suffices h : ∀ l acc, mMapM.loop f l acc = mMapM.loop g l.unattach acc from h l []
  intro l acc
  induction l generalizing acc <;> simp [mMapM.loop, *]

@[wf_preprocess] theorem mMapM_wfParam {xs : List α} {f : α → m β} :
    (wfParam xs).mMapM f = xs.attach.unattach.mMapM f := by
  simp [wfParam]

@[wf_preprocess] theorem mMapM_unattach {P : α → Prop} {xs : List (Subtype P)} {f : α → m β} :
    xs.unattach.mMapM f = xs.mMapM fun ⟨x, h⟩ =>
      binderNameHint x f <| binderNameHint h () <| f (wfParam x) := by
  simp [wfParam]

@[simp] theorem mFilterMapM_subtype {p : α → Prop} {l : List {x // p x}}
    {f : {x // p x} → m (Option β)} {g : α → m (Option β)} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    l.mFilterMapM f = l.unattach.mFilterMapM g := by
  suffices h : ∀ l acc, mFilterMapM.loop f l acc = mFilterMapM.loop g l.unattach acc from h l []
  intro l acc
  induction l generalizing acc <;> simp [mFilterMapM.loop, *]

@[wf_preprocess] theorem mFilterMapM_wfParam {xs : List α} {f : α → m (Option β)} :
    (wfParam xs).mFilterMapM f = xs.attach.unattach.mFilterMapM f := by
  simp [wfParam]

@[wf_preprocess] theorem mFilterMapM_unattach
    {P : α → Prop} {xs : List (Subtype P)} {f : α → m (Option β)} :
    xs.unattach.mFilterMapM f = xs.mFilterMapM fun ⟨x, h⟩ =>
      binderNameHint x f <| binderNameHint h () <| f (wfParam x) := by
  simp [wfParam]

@[simp] theorem mFlatMapM_subtype {p : α → Prop} {l : List {x // p x}}
    {f : {x // p x} → m (List β)} {g : α → m (List β)} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    l.mFlatMapM f = l.unattach.mFlatMapM g := by
  suffices h : ∀ l acc, mFlatMapM.loop f l acc = mFlatMapM.loop g l.unattach acc from h l []
  intro l acc
  induction l generalizing acc <;> simp [mFlatMapM.loop, *]

@[wf_preprocess] theorem mFlatMapM_wfParam {xs : List α} {f : α → m (List β)} :
    (wfParam xs).mFlatMapM f = xs.attach.unattach.mFlatMapM f := by
  simp [wfParam]

@[wf_preprocess] theorem mFlatMapM_unattach
    {P : α → Prop} {xs : List (Subtype P)} {f : α → m (List β)} :
    xs.unattach.mFlatMapM f = xs.mFlatMapM fun ⟨x, h⟩ =>
      binderNameHint x f <| binderNameHint h () <| f (wfParam x) := by
  simp [wfParam]

end List
