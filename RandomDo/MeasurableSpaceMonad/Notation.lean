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
`do` elaborators for binding, branching, mutation, and early return, supplying the additional
measurable-space argument when constructing a computation type or operation.

## Main definitions

* `RandomDo.RDo.randOps`: adapts Lean's `DoOps` to measurable space monad operations.
* `RandomDo.RDo.elabRand`: elaborates an `rdo` block using `randOps`.

## Notation

* `rdo ...`: a monadic program using `RandomDo.MeasurableSpacePure.mPure` and
  `RandomDo.MeasurableSpaceBind.mBind`.

Use `open RandomDo` (or `open scoped RandomDo`) to enable the notation.
-/

open Lean Lean.Parser Lean.Parser.Term Lean.Meta Lean.Elab Lean.Elab.Do Lean.Elab.Term Std Meta
open RandomDo MeasurableSpacePure MeasurableSpaceBind

public meta section

namespace RandomDo

/-- The `do` notation for writing monadic programs depending on a `MeasurableSpace` instance. -/
scoped syntax (name := randKind) (priority := high) "rdo" doSeq : term

namespace RDo

/-- Define `DoOp`s for `rdo` notation. -/
def randOps : DoOps := { DoOps.default with
  mkPureApp α e := do
    let ⟨m, u, v, _, _⟩ := (← read).monadInfo
    let α ← Term.ensureHasType (mkSort (mkLevelSucc u)) α
    let e ← Term.ensureHasType α e
    let instPure ← mkInstMVar (.app (mkConst ``MeasurableSpacePure [u,v]) m)
    let instPure ← instantiateMVars instPure
    let σ ← mkInstMVar (.app (mkConst ``MeasurableSpace [u]) α)
    let σ ← instantiateMVars σ
    return mkAppN (mkConst ``mPure [u, v]) #[m, instPure, α, σ, e]
  mkBindApp α β e k := do
    let ⟨m, u, v, _, _⟩ := (← read).monadInfo
    let α ← Term.ensureHasType (mkSort (mkLevelSucc u)) α
    let σα ← mkInstMVar (.app (mkConst ``MeasurableSpace [u]) α)
    let σβ ← mkInstMVar (.app (mkConst ``MeasurableSpace [u]) β)
    let mα := mkApp2 m α σα
    let mβ := mkApp2 m β σβ
    let e ← Term.ensureHasType mα e
    let k ← Term.ensureHasType (← mkArrow α mβ) k
    let σα ← instantiateMVars σα
    let σβ ← instantiateMVars σβ
    let instBind ← mkInstMVar (.app (mkConst ``MeasurableSpaceBind [u, v]) m)
    let instBind ← instantiateMVars instBind
    return mkAppN (mkConst ``mBind [u, v]) #[m, instBind, α, β, σα, σβ, e, k]
  isPureApp? e :=
    if e.isAppOfArity ``mPure 5 then some (e.getArg! 4) else none
  splitMonadApp? type := do
    let .app m _ := type.consumeMData | return none
    let .app m resultType := m.consumeMData | return none
    unless ← isType resultType do return none
    let u ← getDecLevel resultType
    let v ← getDecLevel type
    return some ({ m := m, u := u.normalize, v := v.normalize }, resultType)
  mkMonadApp α := do
    let ⟨m, u, _, _, _⟩ := (← read).monadInfo
    let σ ← mkInstMVar (mkApp (mkConst ``MeasurableSpace [u]) α)
    return mkApp2 m α σ
  }

/-- Define `rdo` notation elaborator. -/
@[term_elab randKind] def elabRand : Term.TermElab := fun stx et? => do
  let `(rdo $doSeq) := stx | throwUnsupportedSyntax
  elabDoWith randOps doSeq et?

end RDo

end RandomDo
