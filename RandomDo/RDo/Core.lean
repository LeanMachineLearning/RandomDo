/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Lean.Elab.BuiltinDo
meta import Lean.Elab.Tactic.Do.Contract
meta import RandomDo.WP.MeasurableSpaceMonad
public import RandomDo.MeasurableSpaceMonad.Defs

/-!
# `rdo` notation

This file defines `rdo` notation for computations in a measurable space monad, where
`MeasurableSpacePure.mPure` and `MeasurableSpaceBind.mBind` take the roles of `Pure.pure` and
`Bind.bind` respectively. Use `open MeasureTheory` (or `open scoped MeasureTheory`) to enable the
notation.
-/

open Lean Lean.Parser Lean.Parser.Term Lean.Meta Lean.Elab Lean.Elab.Do Lean.Elab.Term Std Meta
open MeasureTheory

public meta section

namespace MeasureTheory

/-- `rdo` is the `do` notation for writing monadic programs in a measurable space monad. -/
scoped syntax (name := rdo) "rdo" doSeq : term

namespace RDo

/-- The `DoOps` for `rdo` notation at the given initial metavariable-context depth.
Analogue of `do` notation's `Lean.Elab.Do.DoOps.default`. -/
def randOps (mctxDepth : Nat) : DoOps where
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
    -- To determine the result type of a dependent match branch, core's
    -- `elabDoSeqWithRefinedType` calls `mkMonadApp` with a temporary unknown type `?α`.
    -- If `Term.mkInstMVar` cannot yet find `MeasurableSpace ?α`, it records a request to try
    -- again later. Core discards the temporary metavariables after this check, but keeps
    -- that request. Trying it later then fails with "unknown metavariable".
    --
    -- We therefore try instance synthesis as usual, but only record requests for later at
    -- the depth where this `rdo` block started. Core increases the depth for the temporary
    -- branch check, so its requests are not recorded.

    -- If core also discards these requests, we can replace this code with `Term.mkInstMVar`
    -- and remove the `mctxDepth` parameter. See https://github.com/leanprover/lean4/issues/16561.
    let σ ← mkFreshExprMVar (mkApp (mkConst ``MeasurableSpace [info.u]) α) .synthetic
    unless ← Term.synthesizeInstMVarCore σ.mvarId! do
      if (← getMCtx).depth == mctxDepth then
        Term.registerSyntheticMVarWithCurrRef σ.mvarId! (.typeClass none)
    let σ ← instantiateMVars σ
    Term.tryPostponeIfMVar σ
    return mkApp2 info.m α σ

/-- Extracts `MonadInfo` and monadic result type `α` from the expected type of an `rdo` block `m α`.
Analogue of `do` notation's `Lean.Elab.Do.extractMonadInfo`. -/
private partial def extractMonadInfo (ops : DoOps) (expectedType? : Option Expr) :
    Term.TermElabM (MonadInfo × Expr) := do
  let some expectedType := expectedType? | mkUnknownMonadResult
  let expectedType ← instantiateMVars expectedType
  let rec extract? (type : Expr) : Term.TermElabM (Option (MonadInfo × Expr)) := do
    match (← ops.splitMonadApp? type) with
    | some r => return r
    | none =>
      let typeNew ← whnfCore type
      if typeNew != type then
        extract? typeNew
      else
        if typeNew.getAppFn.isMVar then
          mkUnknownMonadResult
        else match (← unfoldDefinition? typeNew) with
          | some typeNew => extract? typeNew
          | none => return none
  match (← extract? expectedType) with
  | some r => return r
  | none   => throwError "invalid `rdo` notation, expected type is not a measurable monad \
      application{indentExpr expectedType}"
where
  mkUnknownMonadResult : TermElabM (MonadInfo × Expr) := do
    let u ← mkFreshLevelMVar
    let v ← mkFreshLevelMVar
    let mType ← withLocalDeclD `α (mkSort (mkLevelSucc u)) fun α =>
      withLocalDecl `inst .instImplicit (mkApp (mkConst ``MeasurableSpace [u]) α) fun inst =>
        mkForallFVars #[α, inst] (mkSort (mkLevelSucc v))
    let m ← mkFreshExprMVar mType (userName := `m)
    let resultType ← mkFreshExprMVar (mkSort (mkLevelSucc u)) (userName := `α)
    return ({ m, u, v }, resultType)

/-- Create the `Lean.Elab.Do.Context` for `rdo` elaboration from the given expected type
of an `rdo` block. Analogue of `do` notation's `Lean.Elab.Do.mkContext`. -/
def mkContext (expectedType? : Option Expr) (ops : DoOps) :
    TermElabM Do.Context := do
  let (mi, resultType) ← extractMonadInfo ops expectedType?
  let returnCont ← ReturnCont.mkPure resultType
  let contInfo := ContInfo.toContInfoRef { returnCont }
  return { monadInfo := mi, doBlockResultType := resultType, contInfo,
           ops := ops.toDoOpsRef }

/-- Elaborate `rdoSeq` using `ops` for `mPure`/`mBind` construction.
Analogue of `do` notation's `Lean.Elab.Do.elabDoWith`. -/
def elabRDoWith (ops : DoOps) (rdoSeq : DoSeq)
    (expectedType? : Option Expr) : TermElabM Expr := do
  Term.tryPostponeIfNoneOrMVar expectedType?
  let ctx ← mkContext expectedType? (ops := ops)
  let cont ← DoElemCont.mkPure ctx.doBlockResultType
  let res ← elabDoSeq rdoSeq cont |>.run ctx
  -- Synthesizing default instances here is harmful for expressions such as
  -- ```
  -- withTraceNode `Meta.Tactic.solveByElim (return m!"{exceptEmoji ·} trying to apply: {e}") do
  --   ... (g.apply e cfg) ...
  -- ```
  -- Doing so will default the type of `e` to `MessageData` as part of elaborating the `return`
  -- expression before elaboration can propagate that `e : Expr` in the `apply` call.
  -- Term.synthesizeSyntheticMVarsUsingDefault
  trace[Elab.do] "{← instantiateMVars res}"
  pure res

/-- The `rdo` notation elaborator. Analogue of `do` notation's `Lean.Elab.Do.elabDo`. -/
@[term_elab «rdo»] def elabRDo : Term.TermElab := fun e expectedType? => do
  let `(rdo $rdoSeq) := e | throwError "unexpected `rdo` block syntax{indentD e}"
  elabRDoWith (randOps (← getMCtx).depth) rdoSeq expectedType?

/-- Elaborate a terminal pattern binding with a fallback in `rdo`.
This delegates to `Lean.Elab.Do.elabDoLetElse`, using `mPure PUnit.unit` in place of
core's default success body, `pure PUnit.unit`. -/
@[doElem_elab Lean.Parser.Term.doLetElse]
def elabRDoLetElse : DoElab := fun stx dec => do
  let `(doLetElse| let%$tk $[mut%$mutTk?]? $cfg:letConfig $pattern := $rhs | $otherwise) := stx
    | throwUnsupportedSyntax
  let expectedType ← mkMonadApp dec.resultType
  unless (← (randOps (← getMCtx).depth).splitMonadApp? expectedType).isSome do
    throwUnsupportedSyntax
  let body ← `(doSeqIndent| mPure PUnit.unit)
  let stx ←
    `(doLetElse| let%$tk $[mut%$mutTk?]? $cfg:letConfig $pattern := $rhs | $otherwise $(some body)?)
  Lean.Elab.Do.elabDoLetElse ⟨stx⟩ dec

/-- Elaborate a verification assertion using the measurable monad's WP interpretation.
Analogue of `do` notation's `Lean.Elab.Tactic.Do.elabDoAssertion`. -/
@[doElem_elab Lean.Parser.Term.doAssertion]
def elabRDoAssertion : DoElab := fun stx dec => do
  let expectedType ← mkMonadApp (← mkPUnit)
  unless (← (randOps (← getMCtx).depth).splitMonadApp? expectedType).isSome do
    throwUnsupportedSyntax
  let tk := stx.raw[0]
  let as : Term ← match stx with
    | `(doAssertion| assert $f:basicFun) => `(fun $f:basicFun)
    | `(doAssertion| assert $p:term) => pure p
    | _ => throwUnsupportedSyntax
  unless (← getEnv).contains ``MeasureTheory.WP.assertGadget do
    throwErrorAt tk
      "the `assert` element elaborates to a `vcgen` gadget; \
      add `import RandomDo.WP.MeasurableSpaceMonad` to use it."
  warnIntrinsicExperimental tk m!"`assert` element"
  let dec ← dec.ensureUnitAt tk
  let e ← Term.elabTermEnsuringType
    (← `(open scoped Std.WP Lean.Order in $(mkCIdent ``MeasureTheory.WP.assertGadget) $as))
    expectedType
  dec.mkBindUnlessPure e

end RDo

end MeasureTheory
