/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.MeasurableSpaceMonad.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Prod
public meta import Lean.Elab.BuiltinDo

/-!
# `rdo` notation

This file defines `rdo` notation for computations in a measurable space monad, where
`MeasurableSpacePure.mPure` and `MeasurableSpaceBind.mBind` take the roles of `Pure.pure` and
`Bind.bind` respectively. Use `open MeasureTheory` (or `open scoped MeasureTheory`) to enable the
notation.
-/

open Lean Lean.Parser Lean.Parser.Term Lean.Meta Lean.Elab Lean.Elab.Do Lean.Elab.Term Std Meta
open MeasureTheory MeasurableSpacePure MeasurableSpaceBind

public meta section

namespace MeasureTheory

/-- `rdo` is the `do` notation for writing monadic programs in a measurable space monad. -/
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
    let .app m σ := type.consumeMData | return none
    let .app m resultType := m.consumeMData | return none
    unless ← isType resultType do return none
    let σType ← whnf (← inferType σ)
    unless σType.isAppOf ``MeasurableSpace do return none
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
