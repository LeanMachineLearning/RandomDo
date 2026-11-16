/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.MeasurableSpaceMonad.ForIn
public import Mathlib.MeasureTheory.MeasurableSpace.Prod
public meta import Lean.Elab.BuiltinDo
public meta import Lean.Elab.Do.PatternVar
public meta import Lean.Meta.ProdN

/-!
# `rdo` Notation

**TODO**

-/

open Lean Lean.Parser Lean.Parser.Term Lean.Meta Lean.Elab Lean.Elab.Do Lean.Elab.Term Std Meta

open MeasureTheory MeasurableSpacePure MeasurableSpaceBind

public meta section

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
    -- Core can retain this type across elaboration backtracking. Resolve the instance before
    -- returning it, or postpone if its type is not yet determined.
    let σ ← instantiateMVars σ
    Term.tryPostponeIfMVar σ
    return mkApp2 m α σ
  }

/-- The `do` notation for writing monadic programs depending on a `MeasurableSpace` instance. -/
syntax (name := randKind) "rdo" doSeq : term

/-- Define `rdo` notation elaborator. -/
@[term_elab randKind] def elabRand : Term.TermElab := fun stx et? => do
  let `(rdo $doSeq) := stx | throwUnsupportedSyntax
  elabDoWith randOps doSeq et?

section MatchElab

-- Adapted from Lean v4.35.0's `Lean/Elab/BuiltinDo/Match.lean`. The refinement probe additionally
-- restores the term elaboration state so pending instance requests cannot outlive their
-- metavariables.

private def elabDoSeqWithRefinedType (type : Expr) (doSeq : DoSeq) (dec : DoElemCont) :
    DoElabM Expr := do
  -- The refinement probe may register pending instances through `mkMonadApp`. Restore the
  -- term elaboration state as well as the metavariables when leaving this temporary scope.
  let newDoBlockResultType ← mapTermElabM Term.withoutModifyingElabMetaStateWithInfo <|
    withNewMCtxDepth do
    let γ ← mkFreshExprMVar (mkSort (← read).monadInfo.u.succ)
    unless ← isDefEqGuarded type (← mkMonadApp γ) do
      throwError "Could not determine dependently-refined result type of `do` block.\n
        Expected type {type} was not def eq to {← mkMonadApp γ}"
    instantiateMVars γ
  trace[Elab.do.match] "newDoBlockResultType: {newDoBlockResultType}"
  -- The `doBlockResultType` *is* the continuation's return type, since it is duplicable.
  let dec := { dec with resultType := newDoBlockResultType }
  withRefinedResultType newDoBlockResultType (elabDoSeq doSeq dec)

/-- Expand a dependent `match` into a term-level match.
Analogue of `do` notation's `Lean.Elab.Do.expandToTermMatch`. -/
private def expandToTermMatch : DoElab := fun stx dec => do
  let `(doMatch| match $[(dependent := $dep?)]? $[(generalizing := $gen?)]?
    $[(motive := $motive?)]? $discrs:matchDiscr,* with $alts:matchAlt*) := stx
    | throwUnsupportedSyntax
  let doBlockResultType := (← read).doBlockResultType
  let mγ ← mkMonadApp doBlockResultType
  let info ← inferControlInfoElem stx
  let dependent := dep?.getD ⟨.missing⟩ matches `(trueVal| true)
  trace[Elab.do.match] "expandToTermMatch. dependent: {dependent}, \
    doBlockResultType: {doBlockResultType}, dec.resultType: {dec.resultType}"
  let complexDec := withNewMCtxDepth <| not <$> isDefEqGuarded dec.resultType doBlockResultType
  if ← pure dependent <&&> complexDec then
    throwError "Dependent match is not supported when the result type of the `do` block \
      {indentExpr doBlockResultType}\n is different to the result type of the `match` \
      {indentExpr dec.resultType}"
  dec.withDuplicableCont info fun dec => do
  let rec loop i (alts : Array (TSyntax ``matchAlt)) := do
    if h : i < alts.size then
      match alts[i] with
      | `(matchAltExpr| | $patterns,* => $seq) =>
        let vars ← getPatternsVarsEx patterns
        checkMutVarsForShadowing vars
        let elabRhs (type? : Option Expr) : DoElabM Expr := do
          let (true, some type) := (dependent, type?) | elabDoSeq ⟨seq⟩ dec
          elabDoSeqWithRefinedType type ⟨seq⟩ dec
        doElabToSyntaxWithExpectedType m!"match_syntax alternative {patterns.getElems}"
          (ref := seq) elabRhs fun rhs => do
            loop (i + 1) (alts.set i (← `(matchAltExpr| | $patterns,* => $rhs)))
      | _ => throwUnsupportedSyntax
    else
      Term.elabTerm (← `(match $[(generalizing := $gen?)]? $[(motive := $motive?)]?
        $[$discrs],* with $alts:matchAlt*)) mγ
  loop 0 alts

-- cf. Term.expandNonAtomicDiscrs?
private def expandNonAtomicDiscrs? (discrs : TSyntaxArray ``matchDiscr) :
    DoElabM (Option (TSyntaxArray ``matchDiscr)) := do
  -- Recall that
  -- matchDiscr := leading_parser optional (ident >> ":") >> termParser
  if ← discrs.allM fun discr => Term.isAtomicDiscr discr.raw[1] then
    return none
  let mut newDiscrs := #[]
  for discr in discrs do
    let `(matchDiscr| $[$h? :]? $term) := discr | throwUnsupportedSyntax
    if (← Term.isAtomicDiscr term) then
      newDiscrs := newDiscrs.push discr
    else
      trace[Elab.do.match] "elabNonAtomicDiscrs: {term}"
      let e ← Term.elabTerm term none
      let discrNew ← `(matchDiscr| $[$h? :]? $(← Term.exprToSyntax e))
      newDiscrs := newDiscrs.push discrNew
  return some newDiscrs

/-- Elaborate dependent matches in `rdo` with a temporary scope for both elaboration states.
Analogue of `do` notation's `Lean.Elab.Do.elabDoMatch`. -/
@[doElem_elab Lean.Parser.Term.doMatch] def elabRDoDependentMatch : DoElab := fun stx dec => do
  let `(doMatch| match $[(dependent := $dep)]? $[(generalizing := $gen?)]?
    $(motive?)? $discrs,* with $alts:matchAlt*) := stx | throwUnsupportedSyntax
  unless dep.getD ⟨.missing⟩ matches `(trueVal| true) do throwUnsupportedSyntax
  -- Ordinary `do` monads have just one type parameter. Leave their matches to core.
  let ctx ← read
  let .forallE _ _ body _ ← whnf (← inferType ctx.monadInfo.m)
    | throwUnsupportedSyntax
  let .forallE _ instType _ _ ← whnf (body.instantiate1 ctx.doBlockResultType)
    | throwUnsupportedSyntax
  unless (← whnf instType).isAppOf ``MeasurableSpace do throwUnsupportedSyntax
  -- Expand alts
  if let some stxNew ← liftMacroM <| Term.expandMatchAlts? stx then
    return ← Term.withMacroExpansion stx stxNew <| elabDoElem ⟨stxNew⟩ dec
  -- Expand non-atomic discriminants for independent elaboration problems
  if let some discrs ← expandNonAtomicDiscrs? discrs then
    let newStx ← `(doElem| match $[(generalizing := $gen?)]? $(motive?)?
      $discrs,* with $alts:matchAlt*)
    -- We use `mkSaveInfoAnnotation` to make sure the info trees for the discriminants are saved
    -- even if the inner match elaboration is postponed (returning a metavariable).
    -- Without this, `withTermInfoContext'` in `elabDoElemFns` would discard the subtrees
    -- containing TermInfo for variable references in the discriminants.
    return Term.mkSaveInfoAnnotation
      (← Term.withMacroExpansion stx newStx <| elabDoElem ⟨newStx⟩ dec)
  -- Expand simple matches to `let`
  if let `(matchAltExpr| | $y:ident => $seq) := alts.getD 0 ⟨.missing⟩ then
    if let `(matchDiscr| $discr:term) := discrs.getElems.getD 0 ⟨.missing⟩ then
      if alts.size == 1 && (← Term.isPatternVar y) then
        let newStx ← `(doSeq| let $y:ident := $discr; do $(⟨seq⟩))
        return ← Term.withMacroExpansion stx newStx <| elabDoSeq ⟨newStx⟩ dec
  expandToTermMatch stx dec

end MatchElab

section LoopElab

/-- parses `_ : _ in` for `rdo` for loops -/
def rdoForDecl := leading_parser
  Lean.Parser.optional (atomic (Term.ident >> " : ")) >> termParser >> " in " >>
    withForbidden "rdo" termParser

/-- parser for `rdo` for loops -/
@[doElem_parser] def rdoFor := leading_parser
  "for " >> sepBy1 rdoForDecl ", " >> "rdo " >> doSeq

/-- Define expander for loops in `rdo` notation. Note this code mirrors core's implementation for
`do` notation as much as possible. -/
@[macro rdoFor] def expandRDoFor : Macro := fun stx => do
  match stx with
  | `(rdoFor| for $[$_ : ]? $_:ident in $_ rdo $_) =>
    -- This is the target form of the expander, handled by `elabRDoFor` below.
    Macro.throwUnsupported
  | `(rdoFor| for%$tk $decls:rdoForDecl,* rdo $body) =>
    let decls := decls.getElems
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
    doElems := doElems.push (← `(doSeqItem| for%$tk $[$h? : ]? $x:ident in $xs rdo $body))
    `(doElem| do $doElems*)
  | _ => Macro.throwUnsupported

/-- Define loop elaborator for `rdo` notation. Note this code mirrors core's implementation for
`do` notation as much as possible. -/
@[doElem_elab rdoFor] def elabRDoFor : DoElab := fun stx dec => do
  let `(rdoFor| for%$tk $[$h? : ]? $x:ident in $xs rdo $body) := stx | throwUnsupportedSyntax
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
      let defn ← getLocalDeclFromUserName x.getId
      Term.addTermInfo' x.ident defn.toExpr
      -- ForIn forces the mut tuple into the universe mi.u: that of the do block result type.
      -- If we don't do this, then we are stuck on solving constraints such as
      --   `max ?u.46 ?u.47 =?= max (max ?u.22 ?u.46) ?u.47`
      -- It's important we do this as a separate isLevelDefEq check on the decremented level because
      -- otherwise (`ensureHasType (mkSort mi.u.succ)`) we are stuck on constraints like
      --   `max (?u+1) (?v+1) =?= ?u+1`
      let u ← getDecLevel defn.type
      discard <| isLevelDefEq u mi.u
      defs := defs.push defn.toExpr
    if info.returnsEarly && loopMutVars.isEmpty then
      defs := defs.push (mkConst ``Unit.unit)
    return defs
  let (preS, σ) ← mkProdMkN (← useLoopMutVars none) mi.u
  let mσ ← Term.mkInstMVar <| mkApp (mkConst ``MeasurableSpace [mi.u]) σ
  let (app, p?) ← match h? with
    | none =>
      let instForIn ← Term.mkInstMVar <|
          mkApp3 (mkConst ``MeasurableSpaceForIn [uρ, uα, mi.u, mi.v]) mi.m ρ α
      let app := Lean.mkConst ``MeasurableSpaceForIn.forIn [uρ, uα, mi.u, mi.v]
      let app := mkApp8 app mi.m ρ α instForIn σ mσ xs preS
      pure (app, none)
    | some _ =>
      let d ← mkFreshExprMVar (mkApp2 (mkConst ``Membership [uα, uρ]) α ρ) (userName := `d)
      let instForIn ← Term.mkInstMVar <|
          mkApp4 (mkConst ``MeasurableSpaceForIn' [uρ, uα, mi.u, mi.v]) mi.m ρ α d
      let app := Lean.mkConst ``MeasurableSpaceForIn'.forIn' [uρ, uα, mi.u, mi.v]
      let app := mkApp9 app mi.m ρ α d instForIn σ mσ xs preS
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
  let forIn := mkApp app body
  let γ := (← read).doBlockResultType
  let rest ←
    withLocalDeclD s σ fun postS => do mkLambdaFVars #[postS] <| ← do
      bindMutVarsFromTuple loopMutVarNames postS.fvarId! do
        if info.returnsEarly then
          let ret ← getFVarFromUserName returnVarName
          let ret ← if loopMutVars.isEmpty then mkAppM ``Prod.fst #[ret] else pure ret
          /- Both branches produce an `m γ`, so the motive is constant and the matcher generated
          for `Break.runK` is not needed: `Break.runK` itself is that case analysis. Note that it
          takes the `none` branch first, the other way round from the matcher. -/
          let none := mkSimpleThunk (← dec.continueWithUnit)
          let some ← withLocalDeclD (← mkFreshUserName `r) oldReturnCont.resultType fun r => do
            mkLambdaFVars #[r] (← oldReturnCont.k r)
          return mkAppN (mkConst ``Break.runK [mi.u, mi.v])
            #[oldReturnCont.resultType, ← mkMonadApp γ, ret, none, some]
        else
          dec.continueWithUnit
  mkBindApp σ γ forIn rest

end LoopElab

end RDo
