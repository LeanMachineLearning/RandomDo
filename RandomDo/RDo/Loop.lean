/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Gaëtan Serré
-/
module

public meta import Lean.Meta.ProdN
public import RandomDo.ForMathlib.MeasureTheory.MeasurableSpace.Erased
public import RandomDo.ForMathlib.MeasureTheory.MeasurableSpace.Option
public import RandomDo.MeasurableSpaceMonad.ForIn
public import RandomDo.RDo.Core
-- Reuse core's private assertion-binder and loop-state helpers.
meta import all Lean.Elab.BuiltinDo.For
meta import RandomDo.WP.ForIn

/-!
# loops in `rdo` notation

This file defines the syntax, macro expansion, control-flow analysis, and elaboration for `for`,
`repeat`, and `while` loops in `rdo` notation.
-/

open Lean Lean.Parser Lean.Parser.Term Lean.Meta Lean.Elab Lean.Elab.Do Lean.Elab.Term Std Meta
open MeasureTheory

public meta section

namespace MeasureTheory

/-- A declaration in an `rdo` loop. Analogue of `do` notation's `Lean.Parser.Term.doForDecl`. -/
def rdoForDecl := leading_parser
  Lean.Parser.optional (atomic (Term.ident >> " : ")) >> termParser >> " in " >>
    withForbiddens #["rdo", "invariant", "decreasing"] termParser

/--
The optional `invariant` clause of an `rdo` loop, written like a `fun`: the invariant annotates the
loop so `vcgen` reads it from the program, and mutable variables are referenced by name.

On a `for` loop the clause is `invariant pref suff a b c => e`, with `pref` bound to the elements
consumed so far and `suff` to the elements remaining. On a `repeat` or `while` loop it is
`invariant exit a b c => e`, with `exit` bound to whether the loop has left. Any further binders,
here `a b c`, bind the arguments of the assertion itself, such as the state of a state monad.

Analogue of `do` notation's `Lean.Parser.Term.doLoopInvariant`.
-/
def rdoLoopInvariant := leading_parser
  ppIndent (ppLine >> nonReservedSymbol "invariant" >>
    withForbiddens #["rdo", "decreasing"] basicFun)

/--
A `decreasing` clause gives a `repeat` or `while` loop its termination measure, which every
iteration must lower. The measure is a term over the loop's mutable variables; the form
`decreasing a b c => e` binds the arguments of the measure itself, such as the state of a state
monad. Analogue of `do` notation's `Lean.Parser.Term.doLoopDecreasing`.
-/
def rdoLoopDecreasing := leading_parser
  ppIndent (ppLine >> nonReservedSymbol "decreasing" >>
    withForbidden "rdo" (atomic basicFun <|> (ppSpace >> termParser)))

/--
`for x in e rdo s` iterates over `e` assuming `e`'s type has an instance of the
`MeasurableSpaceForIn` typeclass. `break` and `continue` are supported inside `for` loops.
`for x in e, x2 in e2, ... rdo s` iterates over the given collections in parallel,
until at least one of them is exhausted. The types of `e2` etc. must implement the
`Std.ToStream` typeclass. The loop state, including any stream states, must have a
`MeasurableSpace` instance. Analogue of `do` notation's `Lean.Parser.Term.doFor`.
-/
@[scoped doElem_parser] def rdoFor := leading_parser
  "for " >> sepBy1 rdoForDecl ", " >> Lean.Parser.optional rdoLoopInvariant >>
    Lean.Parser.optional rdoLoopDecreasing >> " rdo " >> doSeq

/-- A standalone `rdo` loop. Analogue of `do` notation's `Lean.Parser.Term.termFor`. -/
@[scoped term_parser] def termRDoFor := leading_parser
  "for " >> sepBy1 rdoForDecl ", " >> Lean.Parser.optional rdoLoopInvariant >>
    Lean.Parser.optional rdoLoopDecreasing >> " rdo " >> doSeq

/-- An unbounded `rdo` loop. Analogue of `do` notation's `Lean.Parser.Term.doRepeat`. -/
@[scoped doElem_parser default + 1] def rdoRepeat := leading_parser
  "repeat " >> "rdo " >>
    withForbidden "do" (optional rdoLoopInvariant >> optional rdoLoopDecreasing) >> doSeq

/-- A conditional `rdo` loop. Analogue of `do` notation's `Lean.Parser.Term.doWhile`. -/
@[scoped doElem_parser] def rdoWhile := leading_parser
  "while " >> withForbiddens #["rdo", "invariant", "decreasing"] doIfCond >>
    optional rdoLoopInvariant >> optional rdoLoopDecreasing >> " rdo " >> doSeq

/-- An `rdo` loop with a final test.
Analogue of `do` notation's `Lean.Parser.Term.doRepeatUntil`. -/
@[scoped doElem_parser default + 1] def rdoRepeatUntil := leading_parser
  "repeat " >> "rdo " >>
    withForbidden "do" (optional rdoLoopInvariant >> optional rdoLoopDecreasing) >> doSeq >>
    ppDedent ppLine >> "until " >> termParser

namespace RDo

/-- Wrap a standalone loop in an `rdo` block.
Analogue of `do` notation's `Lean.Elab.Term.expandTermFor`. -/
@[macro termRDoFor] def expandTermRDoFor : Macro := fun stx => do
  let stx := stx.setKind ``rdoFor
  withRef stx `(rdo $(⟨stx⟩):doElem)

/-- Expand loop binders. Analogue of `do` notation's `Lean.Elab.Do.expandDoFor`. -/
@[macro rdoFor] def expandRDoFor : Macro := fun stx => do
  match stx with
  | `(rdoFor| for $[$_ : ]? $_:ident in $_
      $[$_inv:rdoLoopInvariant]? $[$_dec:rdoLoopDecreasing]? rdo $_) =>
    -- This is the target form of the expander, handled by `elabRDoFor` below.
    Macro.throwUnsupported
  | `(rdoFor| for%$tk $decls:rdoForDecl,*
      $[$inv:rdoLoopInvariant]? $[$dec:rdoLoopDecreasing]? rdo $body) =>
    let decls := decls.getElems
    if let some inv := inv then
      if decls.size > 1 then
        Macro.throwErrorAt inv "The `invariant` clause takes a `for` loop over a single collection."
    let `(rdoForDecl| $[$h? : ]? $pattern in $xs) := decls[0]! | Macro.throwUnsupported
    let mut doElems := #[]
    let mut body := body
    -- Expand `pattern` into an `Ident` `x`:
    let x ←
      if pattern.raw.isIdent then
        pure ⟨pattern⟩
      else if pattern.raw.isOfKind ``Lean.Parser.Term.hole then
        Term.mkFreshIdent pattern
      else
        -- This case is a last resort, because it introduces a `match` and that will cause eager
        -- defaulting. In practice this means that `mut` vars default to `Nat` too often.
        -- Hence we try to only generate a `match` if we absolutely must.
        let x ← Term.mkFreshIdent pattern
        body ← `(doSeq| match $x:term with | $pattern => $body)
        pure x
    -- Expand the remaining `rdoForDecl`s:
    for rdoForDecl in decls[1...*] do
      /-
        Expand
        ```
        for x in xs, y in ys rdo
          body
        ```
        into
        ```
        let mut s := Std.toStream ys
        for x in xs rdo
          match Std.Stream.next? s with
          | none => break
          | some (y, s') =>
            s := s'
            body
        ```
      -/
      let `(rdoForDecl| $[$h? : ]? $y in $ys) := rdoForDecl | Macro.throwUnsupported
      if let some h := h? then
        Macro.throwErrorAt h "The proof annotation here has not been implemented yet."
      /- Recall that `@` (explicit) disables `coeAtOutParam`.
         We used `@` at `Stream` functions to make sure `resultIsOutParamSupport` is not used. -/
      let toStreamApp ← withRef ys `(@Std.toStream _ _ _ $ys)
      let s := mkIdentFrom ys (← withFreshMacroScope <| MonadQuotation.addMacroScope `__s)
      doElems := doElems.push (← `(doSeqItem| let mut $s := $toStreamApp:term))
      body ← `(doSeq|
        match @Std.Stream.next? _ _ _ $s with
          | none => break
          | some ($y, s') =>
            $s:ident := s'
            do $body)
    doElems := doElems.push
      (← `(doSeqItem| for%$tk $[$h? : ]? $x:ident in $xs
        $[$inv:rdoLoopInvariant]? $[$dec:rdoLoopDecreasing]? rdo $body))
    `(doElem| do $doElems*)
  | _ => Macro.throwUnsupported

/-- Demand the class that the `invariant` clause's specification is stated over, so that the
container that lacks it is reported at the clause.
Analogue of `do` notation's `Lean.Elab.Do.checkPureForIn`. -/
private def checkPureForIn (invClause : Syntax) (h? : Option Syntax) (xs α : Expr)
    (mi : MonadInfo) : DoElabM Unit := withRef invClause do
  let cls := if h?.isSome then `MeasureTheory.Internal.PureMeasurableSpaceForIn'
    else `MeasureTheory.Internal.PureMeasurableSpaceForIn
  unless (← getEnv).contains cls do return
  let ty ← Term.elabType <| ←
    `($(mkIdent cls) $(← Term.exprToSyntax mi.m) $(← Term.exprToSyntax (← inferType xs))
      $(← Term.exprToSyntax α))
  discard <| Term.mkInstMVar ty
    (extraErrorMsg? := m!"The `invariant` clause is stated over this class, which says that \
      iterating the container produces its elements without effects.")

/-- The assertion language of the `rdo` block's monad, which `WPMeasurableSpaceMonad` computes as an
output parameter: synthesizing `WPMeasurableSpaceMonad Measure _ _` assigns `ℝ≥0∞` for the
quantitative assertions of `Measure`. The result is what the monad's assertions are known to be
right here, so a monad whose instance is not available reports nothing. The class's arguments are
fresh natural metavariables that the found instance assigns, so the query registers no pending
instance goals. Analogue of `do` notation's `Lean.Elab.Do.assertionLanguage?`.

Compared to core, aliases along the assertion type's function arguments are unfolded so the
shared helpers correctly count and type assertion binders. -/
private def assertionLanguage? : DoElabM (Option Expr) := do
  unless (← getEnv).contains ``MeasureTheory.WPMeasurableSpaceMonad do return none
  let wpMonad ← mkConstWithFreshMVarLevels ``MeasureTheory.WPMeasurableSpaceMonad
  let (args, _, _) ← forallMetaTelescope (← inferType wpMonad)
  let some m := args[0]? | return none
  unless ← isDefEq m (← read).monadInfo.m do return none
  let .some _ ← trySynthInstance (mkAppN wpMonad args) | return none
  let some pred := args[1]? | return none
  let pred ← instantiateMVars pred
  if pred.hasExprMVar then return none
  some <$> forallTelescopeReducing pred fun args result => mkForallFVars args result

/-- Elaborate the gadget application that replaces the loop. The gadgets live downstream of this
module, so `gadget` is an unresolved name that resolves in the user's context.
Adapted from `do` notation's `Lean.Elab.Do.ForInApp.mkCall` to construct the expected type
using `mkMonadApp g.σ`, respecting the supplied `DoOps`. -/
private def mkForInCall (g : ForInApp) (ref : Syntax) (gadget : Name)
    (annotations : Array Term) : DoElabM Expr := do
  unless (← getEnv).contains gadget do
    throwErrorAt ref "a loop annotation elaborates to a `vcgen` gadget; \
      add `import RandomDo.WP.ForIn` to use it."
  -- `open scoped` activates the instances of `Std.WP` and the notation of `Lean.Order` for the
  -- annotations, as the contract's spec theorem does for the `requires` and `ensures` clauses.
  let call ← `(open scoped Std.WP Lean.Order in
    $(mkIdent gadget) $(← Term.exprToSyntax g.xs) $(← Term.exprToSyntax g.init)
      $(← Term.exprToSyntax g.body) $annotations*)
  Term.elabTermEnsuringType call (← mkMonadApp g.σ)

/-- The binders and body of an `invariant` clause. An ascription covering the binder list would
cover the loop's binders and the assertion's alike, so it is reported here.
Analogue of `do` notation's `Lean.Elab.Do.destructInvariant`. -/
private def destructInvariant (invClause : TSyntax ``rdoLoopInvariant) :
    DoElabM (TSyntaxArray ``Lean.Parser.Term.funBinder × Term) := do
  if let `(rdoLoopInvariant| invariant $_* : $ty => $_) := invClause then
    throwErrorAt ty "The `invariant` clause takes no type ascription covering all its binders; \
      ascribe the type on an individual binder, as in `invariant (pref : List α) suff => ...`."
  let `(rdoLoopInvariant| invariant $binders* => $body) := invClause | throwUnsupportedSyntax
  return (binders, body)

/-- Rebuild the loop over a collection as a `mForInPureWithInvariant` call carrying the `invariant`
clause, or `mForInPureWithInvariant'` for a membership-proof binder (`for h : x in xs`). The
invariant names the loop's mutable variables directly; its first two binders are the elements
consumed so far and the elements remaining, and binders past them bind the arguments of the
assertion itself. Analogue of `do` notation's `Lean.Elab.Do.mkForInPureWithInvariant`. -/
private def mkForInPureWithInvariant (g : ForInApp) (invClause : TSyntax ``rdoLoopInvariant)
    (h? : Option Ident) (α : Expr) : DoElabM Expr := do
  let (binders, invBody) ← destructInvariant invClause
  checkPureForIn invClause h? g.xs α (← read).monadInfo
  unless binders.size ≥ 2 do
    throwErrorAt invClause "The `invariant` clause takes at least two binders: the elements \
      consumed so far and the elements remaining."
  let loopBinders := binders.take 2
  let assertionBinders := binders.drop 2
  let pred? ← assertionLanguage?
  checkAssertionBinders invClause "invariant" assertionBinders.size pred?
  let invBody ← mkAssertionFun assertionBinders invBody pred?
  let invLam ← `(fun $loopBinders* => $(← g.mkStateFun invBody))
  let gadget := if h?.isSome then ``MeasureTheory.WP.mForInPureWithInvariant'
    else ``MeasureTheory.WP.mForInPureWithInvariant
  mkForInCall g invClause gadget #[invLam]

/-- Rebuild the loop of a `repeat rdo` as a call to the gadget carrying the annotations the loop
states. Both clauses name the loop's mutable variables directly. The `invariant` clause takes the
`Bool` that says whether the loop has left, followed by the state tuple, which the mutable variables
already name. Analogue of `do` notation's `Lean.Elab.Do.mkForInLoopGadget`.
-/
private def mkForInLoopGadget (g : ForInApp)
    (inv? : Option (TSyntax ``rdoLoopInvariant)) (dec? : Option (TSyntax ``rdoLoopDecreasing)) :
    DoElabM (Option Expr) := do
  let pred? ← assertionLanguage?
  let invArg? ← inv?.mapM fun invClause => do
    let (binders, invBody) ← destructInvariant invClause
    let exitBinder := binders[0]!
    let assertionBinders := binders.drop 1
    checkAssertionBinders invClause "invariant" assertionBinders.size pred?
    let invBody ← mkAssertionFun assertionBinders invBody pred?
    let exitVar := mkIdentFrom invClause (← mkFreshUserName `__exit)
    let invBody ← if exitBinder.raw.isOfKind ``hole then pure invBody else
      let exitPat : Term := ⟨exitBinder.raw⟩
      `(match $exitVar:ident with | $exitPat => $invBody)
    -- `WhileInvariant.mk` keeps the clause's declared type on the term. A bare lambda carries the
    -- unfolded type, and a specification's instance arguments are synthesized before the check that
    -- would unfold it.
    return ((invClause : Syntax), ← `($(mkIdent ``Std.WP.WhileInvariant.mk)
      fun $exitVar:ident $(g.statePat) => $(← g.wrapErasedProjs invBody)))
  let varArg? ← dec?.mapM fun decClause => do
    let (binders, body) ← match decClause with
      | `(rdoLoopDecreasing| decreasing $binders* => $body) => pure (binders, body)
      | `(rdoLoopDecreasing| decreasing $measure:term) => pure (#[], measure)
      | _ => throwUnsupportedSyntax
    checkAssertionBinders decClause "measure" binders.size pred?
    return ((decClause : Syntax), ← g.mkStateFun (← mkAssertionFun binders body pred?))
  let some (ref, gadget, annotations) := (match invArg?, varArg? with
    | some (ref, inv), some (_, var) =>
      some (ref, ``MeasureTheory.WP.mForInLoopWithInvariantAndVariant, #[inv, var])
    | some (ref, inv), none => some (ref, ``MeasureTheory.WP.mForInLoopWithInvariant, #[inv])
    | none, some (ref, var) => some (ref, ``MeasureTheory.WP.mForInLoopWithVariant, #[var])
    | none, none => none) | return none
  some <$> mkForInCall g ref gadget annotations

/--
Infer a loop's control effects.
Analogue of the `for` case in `do` notation's `Lean.Elab.Do.InferControlInfo.ofElem`.
-/
@[doElem_control_info rdoFor] def controlInfoRDoFor : ControlInfoHandler := fun stx => do
  let `(rdoFor| for $[$_ : ]? $_:ident in $_
      $[$_:rdoLoopInvariant]? $[$_:rdoLoopDecreasing]? rdo $body) := stx | throwUnsupportedSyntax
  let info ← inferControlInfoSeq body
  return { info with  -- keep only reassigns and returnsEarly
    numRegularExits := 1,
    continues := false,
    breaks := false,
    noFallthrough := false,
  }

/-- Elaborate a loop. Analogue of `do` notation's `Lean.Elab.Do.elabDoFor`. -/
@[doElem_elab rdoFor] def elabRDoFor : DoElab := fun stx dec => do
  let `(rdoFor| for%$tk $[$h? : ]? $x:ident in $xs
      $[$inv?:rdoLoopInvariant]? $[$dec?:rdoLoopDecreasing]? rdo $body) := stx
    | throwUnsupportedSyntax
  if let some invClause := inv? then
    warnIntrinsicExperimental invClause.raw[0] m!"`invariant` clause"
  if let some decClause := dec? then
    warnIntrinsicExperimental decClause.raw[0] m!"`decreasing` clause"
  let dec ← dec.ensureUnitAt tk
  checkMutVarsForShadowing #[x]
  let uα ← mkFreshLevelMVar
  let uρ ← mkFreshLevelMVar
  let α ← mkFreshExprMVar (mkSort (uα.succ)) (userName := `α) -- assigned by outParam
  let ρ ← mkFreshExprMVar (mkSort (uρ.succ)) (userName := `ρ) -- assigned in the next line
  let xs ← Term.elabTermEnsuringType xs ρ
  let mi := (← read).monadInfo
  let mutVars := (← read).mutVars
  let info ← inferControlInfoSeq body
  let oldReturnCont ← getReturnCont
  let returnVarName ← mkFreshUserName `__r
  let loopMutVars := mutVars.filter fun x => info.reassigns.contains x.getId
  let loopMutVarNames :=
    if info.returnsEarly then
      returnVarName :: (loopMutVars.map (·.getId)).toList
    else
      (loopMutVars.map (·.getId)).toList
  let useLoopMutVars (e : Option Expr) : TermElabM (Array Expr) := do
    let mut defs := #[]
    unless e.isNone || info.returnsEarly do
      throwError "Early returning {e} but the info said there is no early return"
    if info.returnsEarly then
      let returnVar ←
        match e with
        | none => mkNone oldReturnCont.resultType
        | some e => mkSome oldReturnCont.resultType e
      defs := defs.push returnVar
    for x in loopMutVars do
      Term.addTermInfo' x.ident (← getFVarFromUserName x.getId)
      let v ← x.stateValue
      -- ForIn forces the mut tuple into the universe mi.u: that of the do block result type.
      -- If we don't do this, then we are stuck on solving constraints such as
      --   `max ?u.46 ?u.47 =?= max (max ?u.22 ?u.46) ?u.47`
      -- It's important we do this as a separate isLevelDefEq check on the decremented level because
      -- otherwise (`ensureHasType (mkSort mi.u.succ)`) we are stuck on constraints like
      --   `max (?u+1) (?v+1) =?= ?u+1`
      let u ← getDecLevel (← inferType v)
      discard <| isLevelDefEq u mi.u
      defs := defs.push v
    if info.returnsEarly && loopMutVars.isEmpty then
      defs := defs.push (mkConst ``Unit.unit)
    return defs
  let (preS, σ) ← mkProdMkN (← useLoopMutVars none) mi.u
  -- Only the loop state needs a measurable space. In a comma-separated loop this includes
  -- the stream states introduced by `expandRDoFor`.
  let mσ ← Term.mkInstMVar <| mkApp (mkConst ``MeasurableSpace [mi.u]) σ
  let (app, p?) ← match h? with
    | none =>
      let instForIn ← Term.mkInstMVar <|
        mkApp3 (mkConst ``MeasurableSpaceForIn [uρ, uα, mi.u, mi.v]) mi.m ρ α
      let app := Lean.mkConst ``MeasurableSpaceForIn.mForIn [uρ, uα, mi.u, mi.v]
      let app := mkApp8 app mi.m ρ α instForIn σ mσ xs preS -- 1 arg remaining: loop body
      pure (app, none)
    | some _ =>
      let d ← mkFreshExprMVar (mkApp2 (mkConst ``Membership [uα, uρ]) α ρ) (userName := `d)
      let instForIn ← Term.mkInstMVar <|
        mkApp4 (mkConst ``MeasurableSpaceForIn' [uρ, uα, mi.u, mi.v]) mi.m ρ α d
      let app := Lean.mkConst ``MeasurableSpaceForIn'.mForIn' [uρ, uα, mi.u, mi.v]
      let app := mkApp9 app mi.m ρ α d instForIn σ mσ xs preS -- 1 arg remaining: loop body
      pure (app, some d)
  let s ← mkFreshUserName `__s
  let xh : Array (Name × (Array Expr → DoElabM Expr)) := match h?, p? with
    | some h, some d =>
      #[(x.getId, fun _ => pure α),
        (h.getId, fun x => pure (mkApp5 (mkConst ``Membership.mem [uα, uρ]) α ρ d xs x[0]!))]
    | _, _ =>
      #[(x.getId, fun _ => pure α)]
  let body ←
    withLocalDeclsD xh fun xh => do
    Term.addLocalVarInfo x xh[0]!
    if let some h := h? then
      Term.addLocalVarInfo h xh[1]!
    withLocalDecl s .default σ (kind := .implDetail) fun loopS => do
    mkLambdaFVars (xh.push loopS) <| ← do
    bindMutVarsFromTuple loopMutVarNames loopS.fvarId! do
    let newDoBlockResultType := mkApp (mkConst ``ForInStep [mi.u]) σ
    withDoBlockResultType newDoBlockResultType do
    let continueCont := do
      let (tuple, _tupleTy) ← mkProdMkN (← useLoopMutVars none) mi.u
      let yield := mkApp2 (mkConst ``ForInStep.yield [mi.u]) σ tuple
      mkPureApp newDoBlockResultType yield
    let breakCont := do
      let (tuple, _tupleTy) ← mkProdMkN (← useLoopMutVars none) mi.u
      let done := mkApp2 (mkConst ``ForInStep.done [mi.u]) σ tuple
      mkPureApp newDoBlockResultType done
    let returnCont := { oldReturnCont with k := fun e => do
        let (tuple, _tupleTy) ← mkProdMkN (← useLoopMutVars (some e)) mi.u
        let done := mkApp2 (mkConst ``ForInStep.done [mi.u]) σ tuple
        mkPureApp newDoBlockResultType done
      }
    enterLoopBody breakCont continueCont returnCont do
    -- Elaborate the loop body, which must have result type `PUnit`, just like the whole `for` loop.
    elabDoSeq body { dec with k := continueCont, kind := .duplicable }
  -- A loop over `Lean.Loop` is what `repeat` and `while` expand to, and it is the only one whose
  -- termination the program has to state.
  let mut mForIn := mkApp app body
  unless inv?.isNone && dec?.isNone do
    let g : ForInApp :=
      { xs, init := preS, body, σ, statePat := ← mkStatePat loopMutVars info.returnsEarly,
        erasedMutVars := loopMutVars.filter (·.erased) }
    if (← instantiateMVars ρ).isConstOf ``Lean.Loop then
      if let some e ← mkForInLoopGadget g inv? dec? then mForIn := e
    else if let some decClause := dec? then
      throwErrorAt decClause "A `for` loop terminates with the collection it iterates; \
        `decreasing` states the termination measure of a `repeat` or `while` loop."
    else if let some invClause := inv? then
      mForIn ← mkForInPureWithInvariant g invClause h? α
  let γ := (← read).doBlockResultType
  let rest ←
    withLocalDeclD s σ fun postS => do mkLambdaFVars #[postS] <| ← do
      bindMutVarsFromTuple loopMutVarNames postS.fvarId! do
        if info.returnsEarly then
          let ret ← getFVarFromUserName returnVarName
          let ret ← if loopMutVars.isEmpty then mkAppM ``Prod.fst #[ret] else pure ret
          -- Core uses the generated matcher `Break.runK.match_1`. Both branches here produce
          -- `m γ`, so the public `Break.runK` suffices. It takes `none` before `some`.
          let none := mkSimpleThunk (← dec.continueWithUnit)
          let some ← withLocalDeclD (← mkFreshUserName `r) oldReturnCont.resultType fun r => do
            mkLambdaFVars #[r] (← oldReturnCont.k r)
          return mkAppN (mkConst ``Break.runK [mi.u, mi.v])
            #[oldReturnCont.resultType, ← mkMonadApp γ, ret, none, some]
        else
          dec.continueWithUnit
  mkBindApp σ γ mForIn rest

/-- Infer the control effects of `repeat rdo`. Analogue of the `repeat` case in `do`
notation's `Lean.Elab.Do.InferControlInfo.ofElem`. -/
@[doElem_control_info rdoRepeat] def controlInfoRDoRepeat : ControlInfoHandler := fun stx => do
  let `(rdoRepeat| repeat rdo $[$_:rdoLoopInvariant]? $[$_:rdoLoopDecreasing]? $bodySeq) := stx
    | throwUnsupportedSyntax
  let info ← inferControlInfoSeq bodySeq
  return { info with
    numRegularExits := if info.breaks then 1 else 0,
    continues := false,
    breaks := false,
    noFallthrough := !info.breaks,
  }

/-- Elaborate `repeat rdo`. Analogue of `do` notation's `Lean.Elab.Do.elabDoRepeat`. -/
@[doElem_elab rdoRepeat] def elabRDoRepeat : DoElab := fun stx dec => do
  let `(rdoRepeat| repeat%$tk rdo $[$inv?:rdoLoopInvariant]?
      $[$var?:rdoLoopDecreasing]? $seq) := stx
    | throwUnsupportedSyntax
  let mut expanded ←
    `(doElem| for%$tk _ in Loop.mk $[$inv?:rdoLoopInvariant]? $[$var?:rdoLoopDecreasing]? rdo $seq)
  let info ← inferControlInfoSeq seq
  if !info.breaks then
    if !(← Meta.isDefEqGuarded dec.resultType (← mkPUnit)) then
      expanded ← `(doElem| do $expanded:doElem; unreachable!)
  Term.withMacroExpansion stx expanded <|
    withRef expanded <| elabDoElem ⟨expanded⟩ dec

/-- Expand `while ... rdo`. Analogue of `do` notation's `Lean.Elab.Do.expandDoWhile`. -/
@[macro rdoWhile] def expandRDoWhile : Macro
  | `(rdoWhile| while%$tk $cond:doIfCond $[$inv?:rdoLoopInvariant]?
      $[$dec?:rdoLoopDecreasing]? rdo $seq) =>
    `(doElem| repeat%$tk rdo $[$inv?:rdoLoopInvariant]? $[$dec?:rdoLoopDecreasing]?
        if $cond:doIfCond then $seq else break)
  | _ => Macro.throwUnsupported

/-- Expand `repeat rdo ... until`.
Analogue of `do` notation's `Lean.Elab.Do.expandDoRepeatUntil`. -/
@[macro rdoRepeatUntil] def expandRDoRepeatUntil : Macro
  | `(rdoRepeatUntil| repeat%$tk rdo $[$inv?:rdoLoopInvariant]? $[$dec?:rdoLoopDecreasing]?
      $seq until $cond) =>
    `(doElem| repeat%$tk rdo $[$inv?:rdoLoopInvariant]? $[$dec?:rdoLoopDecreasing]?
        do $seq:doSeq
        if $cond then break)
  | _ => Macro.throwUnsupported

end RDo

end MeasureTheory
