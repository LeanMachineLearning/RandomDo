/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.MeasurableSpaceMonad.Core
public import Mathlib.MeasureTheory.MeasurableSpace.Prod
public meta import Lean.Elab.BuiltinDo

/-!
# `rdo` notation

This file defines `rdo` notation for computations in a measurable space monad. It reuses Lean's
`do` elaborators for binding, branching, mutation, and early return, with
`MeasurableSpacePure.mPure` and `MeasurableSpaceBind.mBind` taking the roles of `Pure.pure` and
`Bind.bind`. Use `open MeasureTheory` (or `open scoped MeasureTheory`) to enable the notation.

## Implementation details

Lean's `Lean.Elab.Do.elabDoWith` accepts a `Lean.Elab.Do.DoOps` structure specifying how to
construct monadic operations and how to recognise and construct monad applications. The entry
point `RDo.elabRand` calls this elaborator with `RDo.randOps`, allowing `rdo` to reuse the core
elaborators for the individual statements in a `do` block.

The operations in `RDo.randOps` are adapted from `Lean.Elab.Do.DoOps.default` in Lean core's
`Lean/Elab/Do/Basic.lean`. The main difference is that a measurable space monad has type
`m : (α : Type u) → [MeasurableSpace α] → Type v`, so a computation type `m α` also contains an
implicit `MeasurableSpace α` argument. The adapted operations account for this extra argument
when constructing or recognising computation types, and use `mPure` and `mBind` in place of
`pure` and `bind`. These implementations should follow core line for line wherever possible,
with only the changes needed for measurable space monads.
-/

open Lean Lean.Parser Lean.Parser.Term Lean.Meta Lean.Elab Lean.Elab.Do Lean.Elab.Term Std Meta
open MeasureTheory MeasurableSpacePure MeasurableSpaceBind

public meta section

namespace MeasureTheory

/-- The `do` notation for writing monadic programs depending on a `MeasurableSpace` instance. -/
scoped syntax (name := randKind) "rdo" doSeq : term

namespace RDo

/-- The `DoOps` for `rdo` notation. Analogue of `do` notation's `Lean.Elab.Do.DoOps.default`. -/
def randOps : DoOps where
  mkPureApp α e := do
    let info := (← read).monadInfo
    if (← read).deadCode matches .deadSyntactically then
      -- There is no dead syntax here. Just return a fresh metavariable so that we don't
      -- do the `Term.ensureHasType` check below.
      return ← mkFreshExprMVar (← mkMonadApp α)
    let α ← Term.ensureHasType (mkSort (mkLevelSucc info.u)) α
    let e ← Term.ensureHasType α e
    let instPure ← Term.mkInstMVar (mkApp (mkConst ``MeasurableSpacePure [info.u, info.v]) info.m)
    let instPure ← instantiateMVars instPure
    let σ ← Term.mkInstMVar (mkApp (mkConst ``MeasurableSpace [info.u]) α)
    let σ ← instantiateMVars σ
    return mkApp5 (mkConst ``MeasurableSpacePure.mPure [info.u, info.v]) info.m instPure α σ e
  mkBindApp α β e k := do
    let info := (← read).monadInfo
    let α ← Term.ensureHasType (mkSort (mkLevelSucc info.u)) α
    let σα ← Term.mkInstMVar (mkApp (mkConst ``MeasurableSpace [info.u]) α)
    let σβ ← Term.mkInstMVar (mkApp (mkConst ``MeasurableSpace [info.u]) β)
    let mα := mkApp2 info.m α σα
    let e ← Term.ensureHasType mα e
    let k ← Term.ensureHasType (← mkArrow α (mkApp2 info.m β σβ)) k
    let instBind ← Term.mkInstMVar (mkApp (mkConst ``MeasurableSpaceBind [info.u, info.v]) info.m)
    return mkApp8 (mkConst ``MeasurableSpaceBind.mBind [info.u, info.v])
      info.m instBind α β σα σβ e k
  isPureApp? e :=
    if e.isAppOfArity ``MeasurableSpacePure.mPure 5 then some (e.getArg! 4) else none
  splitMonadApp? type := do
    let .app m _ := type.consumeMData | return none
    let .app m resultType := m.consumeMData | return none
    unless ← isType resultType do return none
    let u ← getDecLevel resultType
    let v ← getDecLevel type
    return some ({ m, u := u.normalize, v := v.normalize }, resultType)
  mkMonadApp α := do
    let info := (← read).monadInfo
    let σ ← Term.mkInstMVar (mkApp (mkConst ``MeasurableSpace [info.u]) α)
    return mkApp2 info.m α σ

/-- The `rdo` notation elaborator. Analogue of `do` notation's `Lean.Elab.Do.elabDo`. -/
@[term_elab randKind] def elabRand : Term.TermElab := fun stx et? => do
  let `(rdo $doSeq) := stx | throwUnsupportedSyntax
  elabDoWith randOps doSeq et?

end RDo

end MeasureTheory
