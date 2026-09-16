/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Measurability
public meta import Lean.LabelAttribute
public import Lean.LabelAttribute

set_option linter.style.header false

/-!
# The `transfer` tactic

A statement about random variables on a probability space `(Ω, P)` pulls back along a
measure-preserving map `f : Ω' → Ω`: the law of `X` under `P` is the law of `fun ω ↦ X (f ω)` under
`P'`, two random variables are independent if and only if their compositions with `f` are, and so
on. Two kinds of lemmas record this.

* A `@[transfer]` lemma states an invariance,
  ```
  S X P ↔ S (fun ω ↦ X (f ω)) P'        or        t X P = t (fun ω ↦ X (f ω)) P'
  ```
  with the hypothesis `hf : MeasurePreserving f P' P` as its first explicit argument, possibly
  followed by side conditions such as the measurability of `X`. The old space is on the left, so
  that rewriting with the lemma only ever needs first-order unification.
* A `@[transfer_forward]` lemma states an implication `S X P → S (fun ω ↦ X (f ω)) P'`, as
  `(h : S X P) (hf : MeasurePreserving f P' P) (side conditions…) : S (fun ω ↦ X (f ω)) P'`, for
  statements that only go one way, such as measurability.

`transfer hf` rewrites the goal with every `@[transfer]` lemma instantiated at `hf`, discharging the
side conditions by `assumption`, `fun_prop` and `measurability`, and closes the goal by
`assumption` if it can. `transfer hf at h` transports a hypothesis instead, by rewriting or, when
nothing rewrites, by a `@[transfer_forward]` lemma, under the binders of `h` if it has any: this
pulls a fact about the old space back to the new one. `transfer hf at h ⊢` does both, the goal
first, since transporting a measurability hypothesis destroys the fact the goal's side conditions
need. A named target that mentions the old space and is left as it was is an error. `transfer`
alone is for the obligation left by `extend_space`: it introduces the new space, the map and the
statement on the new space, transfers the goal, and closes it with that statement.
-/

public meta section

open Lean Meta Elab Tactic

/-- A lemma stating that a probabilistic statement pulls back along a measure-preserving map
`hf : MeasurePreserving f P' P`, in the form `S X P ↔ S (fun ω ↦ X (f ω)) P'` or
`t X P = t (fun ω ↦ X (f ω)) P'`, with `hf` as its first explicit argument, possibly followed by
side conditions. The `transfer` tactic rewrites with all of them. -/
register_label_attr transfer

/-- A lemma transporting a hypothesis along a measure-preserving map, in the form
`(h : S X P) (hf : MeasurePreserving f P' P) (side conditions…) : S (fun ω ↦ X (f ω)) P'`. The
`transfer` tactic uses them on hypotheses that no `@[transfer]` lemma rewrites. -/
register_label_attr transfer_forward

namespace RDo.Tactic

/-- The tactic state together with the message log, which `SavedState.restore` keeps: an attempt
that fails must not leave the errors it logged behind. -/
structure FullState where
  /-- The tactic state. -/
  state : Tactic.SavedState
  /-- The message log. -/
  messages : MessageLog

/-- Save the tactic state and the message log. -/
def saveFullState : TacticM FullState :=
  return ⟨← saveState, (← getThe Core.State).messages⟩

/-- Restore the tactic state and the message log. -/
def FullState.restore (s : FullState) : TacticM Unit := do
  s.state.restore
  modifyThe Core.State fun st ↦ { st with messages := s.messages }

/-- Run `x` with a budget of `n` thousand heartbeats of its own, or the ambient budget if that is
smaller. An attempt that fails, such as `measurability` on a set that is not measurable, must not
exhaust the budget of the declaration for what comes after it. -/
def withHeartbeatBudget {m : Type → Type} {α : Type} [Monad m] [MonadControlT CoreM m]
    [MonadReaderOf Core.Context m] [MonadWithReaderOf Core.Context m] (n : Nat) (x : m α) :
    m α := do
  let ambient := (← readThe Core.Context).maxHeartbeats
  let budget := if ambient == 0 then n * 1000 else min ambient (n * 1000)
  withCurrHeartbeats <| withTheReader Core.Context (fun c ↦ { c with maxHeartbeats := budget }) x

/-- The discharger for the side conditions of `@[transfer]` lemmas: `assumption`, then `fun_prop`
for the measurability of a function and `measurability` for that of a set. A maximum recursion
depth error inside `measurability`, which happens on unprovable goals, is turned into a plain
failure so that it only makes the rewrite fail, and the search runs on a budget of its own so that
such a failure does not exhaust the heartbeats of the declaration. -/
syntax (name := transferDischarger) "transfer_discharger" : tactic

elab_rules : tactic
  | `(tactic| transfer_discharger) => withMainContext do
    let funProps : Array Name := #[``Measurable, ``AEMeasurable,
      ``MeasureTheory.AEStronglyMeasurable, ``MeasureTheory.StronglyMeasurable]
    let head := (← getMainTarget).getForallBody.getAppFn.constName?
    -- `fun_prop` may fail on `AEMeasurable` where it succeeds on `Measurable`.
    let tac ← if head.any funProps.contains then
        `(tactic| first
            | assumption
            | (intros
               first
                 | assumption
                 | fun_prop
                 | (apply Measurable.aemeasurable; fun_prop)
                 | (apply Measurable.aestronglyMeasurable; fun_prop)))
      else `(tactic| first | assumption | (intros; first | assumption | measurability))
    -- Without error recovery, an alternative that fails to elaborate fails instead of logging an
    -- error and going on with `sorry`: nothing a failed discharge tried leaks into the messages.
    tryCatchRuntimeEx (withHeartbeatBudget 10000 <| Tactic.withoutRecover (evalTactic tac)) fun e ↦
      throwError "transfer_discharger: {e.toMessageData}"

/-- The `@[transfer]` lemmas instantiated at `hf`, as `simp` arguments, together with the lemmas
pushing a preimage through set operations and through a random variable, which put the transferred
events in the form `extend_space` uses: `f ⁻¹' s` for an event `s`, and `(fun ω ↦ X (f ω)) ⁻¹' t`
for an event `X ⁻¹' t`. A lemma that does not elaborate at `hf`, for want of an instance on the
measure for example, is left out rather than making the whole rewrite fail. -/
def transferSimpArgs (hf : Term) : TacticM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) := do
  let mut args := #[]
  for n in ← labelled `transfer do
    let s ← saveFullState
    let ok ← tryCatchRuntimeEx
      (do
        -- Postponing keeps a lemma whose instances depend on yet unknown types, such as the
        -- codomain of an integrand, and rejects one whose instances fail outright.
        discard <| Term.withoutErrToSorry <|
          Tactic.elabTerm (← `($(mkIdent n):ident $hf)) none (mayPostpone := true)
        pure true)
      (fun _ ↦ pure false)
    s.restore
    if ok then args := args.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident $hf))
  let extra ← #[``Set.preimage_ofPred_eq, ``Set.preimage_preimage, ``Set.preimage_inter,
    ``Set.preimage_union, ``Set.preimage_compl, ``Set.preimage_sdiff].mapM fun n ↦
      `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  return args ++ extra

/-- Try to close the goal `g` with `tac`, returning its proof. The state is restored on failure,
and a runtime error such as a maximum recursion depth counts as a failure. The attempt runs on a
heartbeat budget of its own. -/
def tryTactic? (g : MVarId) (tac : Syntax) : TacticM (Option Expr) := do
  let s ← saveFullState
  tryCatchRuntimeEx
    (do
      -- Without error recovery, a failure inside a nested `by` is a failure, not a `sorry`.
      let gs ← withHeartbeatBudget (m := TermElabM) 20000 <| Term.withoutErrToSorry <|
        Tactic.run g (evalTactic tac)
      if gs.isEmpty then return some (← instantiateMVars (.mvar g))
      s.restore
      return none)
    (fun _ ↦ do
      s.restore
      return none)

/-- The old space of `hf : MeasurePreserving f P' P`: the type `Ω` and the measure `P`. -/
def oldSpace? (hf : Expr) : MetaM (Option (Expr × Expr)) := do
  let ty ← whnfR (← instantiateMVars (← inferType hf))
  unless ty.isAppOfArity ``MeasureTheory.MeasurePreserving 7 do return none
  let as := ty.getAppArgs
  return some (as[1]!, as[6]!)

/-- Whether `ty` mentions the old space of `hf`, its type or its measure. A statement that does
not has nothing for `transfer` to do, so leaving it as it is is not a failure. When the old space
cannot be read off `hf`, every statement counts as mentioning it. -/
def mentionsOldSpace (hf ty : Expr) : MetaM Bool := do
  let some (Ω, P) ← oldSpace? hf | return true
  let ty ← instantiateMVars ty
  return Ω.occurs ty || P.occurs ty

/-- The head constant of a statement, under its binders. -/
def headUnderBinders (ty : Expr) : MetaM (Option Name) :=
  forallTelescope ty fun _ body ↦ return body.getAppFn.constName?

/-- The head constant of the statement a `@[transfer_forward]` lemma transports: that of the type
of its first explicit argument. -/
def forwardLemmaHead? (n : Name) : MetaM (Option Name) := do
  forallTelescope (← getConstInfo n).type fun xs _ ↦ do
    for x in xs do
      if (← x.fvarId!.getBinderInfo).isExplicit then
        return ← headUnderBinders (← x.fvarId!.getType)
    return none

/-- Transport the hypothesis `h` forward along `hf` with a `@[transfer_forward]` lemma, as
`lemma h hf side…`, the side conditions being discharged by `transfer_discharger`. A hypothesis
with binders, `∀ n, S (X n) P`, is transported under them. Only the lemmas about the head constant
of `h` are tried, so that a definition is transported as itself and not unfolded to what it is
defined as. Returns the statement and proof of the transported hypothesis. -/
def transferForward? (h hf : Expr) : TacticM (Option (Expr × Expr)) := do
  let hfStx ← Term.exprToSyntax hf
  forallTelescope (← instantiateMVars (← inferType h)) fun xs body ↦ do
    let hStx ← Term.exprToSyntax (mkAppN h xs)
    let head := body.getAppFn.constName?
    for n in ← labelled `transfer_forward do
      if let some lemmaHead ← forwardLemmaHead? n then
        unless head == some lemmaHead do continue
      let s ← saveFullState
      let r ← tryCatchRuntimeEx
        (do
          let e ← Term.withoutErrToSorry <|
            Tactic.elabTerm (← `($(mkIdent n):ident $hStx $hfStx)) none
          let (args, bis, concl) ← forallMetaTelescope (← inferType e)
          for (a, bi) in args.zip bis do
            if bi.isInstImplicit then
              a.mvarId!.assign (← synthInstance (← instantiateMVars (← inferType a)))
            else if bi.isExplicit then
              let some _ ← tryTactic? a.mvarId! (← `(tactic| transfer_discharger))
                | throwError "side condition"
          let pf ← instantiateMVars (mkAppN e args)
          -- `g ∘ f` is put in the form `fun ω ↦ g (f ω)`.
          let concl ← instantiateMVars concl
          let concl ← Core.betaReduce (← deltaExpand concl (· == ``Function.comp))
          if pf.hasExprMVar || concl.hasExprMVar then throwError "metavariables"
          pure (some (← mkForallFVars xs concl, ← mkLambdaFVars xs pf)))
        (fun _ ↦ do
          s.restore
          pure none)
      if r.isSome then return r
    return none

/-- Introduce the binders of a `transfer` obligation: everything up to and including the statement
on the new space, which is the binder after the `MeasurePreserving` hypothesis. Returns the new
goal, the map hypothesis and that statement. -/
partial def introTransferObligation (g : MVarId) : MetaM (MVarId × FVarId × FVarId) :=
  go g none
where
  go (g : MVarId) (hf? : Option FVarId) : MetaM (MVarId × FVarId × FVarId) := do
    unless (← instantiateMVars (← g.getType)).isForall do
      throwError "transfer: the goal is not a `transfer` obligation. It should have the form\n  \
        ∀ Ω' [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (f : Ω' → Ω), \
        MeasurePreserving f P' P → T' → T\nbut is{indentExpr (← g.getType)}"
    let (fv, g) ← g.intro1P
    match hf? with
    | some hf => return (g, hf, fv)
    | none =>
      let isMap ← g.withContext do
        return (← whnfR (← fv.getType)).isAppOf ``MeasureTheory.MeasurePreserving
      go g (if isMap then some fv else none)

/-- The `@[transfer]` lemmas at `hf`, as computed by `transferSimpArgs`. -/
abbrev SimpArgs := Array (TSyntax ``Lean.Parser.Tactic.simpLemma)

/-- Rewrite the goal with the `@[transfer]` lemmas. Returns whether the goal changed or was
closed. -/
def rewriteGoal (args : SimpArgs) : TacticM Bool := do
  let g ← getMainGoal
  let before ← instantiateMVars (← g.getType)
  evalTactic (← `(tactic| simp -failIfUnchanged (disch := transfer_discharger) only [$args,*]))
  let gs ← getUnsolvedGoals
  if gs.isEmpty then return true
  return gs[0]! != g || (← instantiateMVars (← gs[0]!.getType)) != before

/-- Close the goal by `assumption` if it can be. -/
def closeByAssumption : TacticM Unit := do
  unless (← getUnsolvedGoals).isEmpty do evalTactic (← `(tactic| try assumption))

/-- After the goal has been transferred with `changed` reporting whether it was rewritten: fail if
it is still there, was not rewritten, and mentions the old space. -/
def checkGoalTransferred (hf : Expr) (changed : Bool) : TacticM Unit := do
  if changed || (← getUnsolvedGoals).isEmpty then return
  withMainContext do
    let ty ← getMainTarget
    if ← mentionsOldSpace hf ty then
      throwError "transfer: no `@[transfer]` lemma rewrites the goal{indentExpr ty}\n\
        A side condition, such as the measurability of a random variable, may not have been \
        discharged."

/-- Transfer the goal along `hf`: rewrite it with the `@[transfer]` lemmas, then close it by
`assumption` if possible. Fails if the goal mentions the old space and nothing rewrote it. -/
def transferGoal (args : SimpArgs) (hf : Expr) : TacticM Unit := do
  let changed ← rewriteGoal args
  closeByAssumption
  checkGoalTransferred hf changed

/-- Forward-transport the hypothesis `h`, named `name`, if the rewriting left it as it was. Returns
whether `h` was rewritten or transported. When `strict`, a hypothesis that mentions the old space
and could be neither rewritten nor transported is an error. -/
def forwardHyp (hf : Expr) (h : FVarId) (name : Name) (strict : Bool) : TacticM Bool :=
  withMainContext do
    -- `simp` replaces the hypothesis when it rewrites it, so that either `h` is gone or its name
    -- now denotes a newer hypothesis; otherwise it is still there, as it was.
    let lctx ← getLCtx
    let some d := lctx.find? h | return true
    if lctx.findFromUserName? name |>.any (·.fvarId != h) then return true
    match ← transferForward? d.toExpr hf with
    | some (ty, pf) =>
      let g ← (← getMainGoal).assert d.userName ty pf
      let (_, g) ← g.intro1P
      replaceMainGoal [← g.tryClear h]
      return true
    | none =>
      if strict && (← mentionsOldSpace hf d.type) then
        throwError "transfer: nothing transfers the hypothesis {d.toExpr} :{indentExpr d.type}\n\
          No `@[transfer]` lemma rewrites it and no `@[transfer_forward]` lemma transports it.\n\
          A side condition, such as the measurability of a random variable, may not have been \
          discharged."
      return false

/-- Transfer the hypotheses `hs` along `hf`: rewrite each with the `@[transfer]` lemmas, then
replace each one that did not change by its forward transport by a `@[transfer_forward]` lemma.
All the rewriting comes first, since a forward transport destroys the measurability facts the
rewriting may need. When `strict`, a hypothesis that mentions the old space and is left as it was
is an error. Returns whether some hypothesis changed. -/
def transferHyps (args : SimpArgs) (hf : Expr) (hs : Array FVarId) (strict : Bool) :
    TacticM Bool := do
  if (← getUnsolvedGoals).isEmpty then return false
  let names ← withMainContext do hs.mapM (·.getUserName)
  for h in hs do
    let hStx ← withMainContext do Term.exprToSyntax (.fvar h)
    evalTactic (← `(tactic|
      simp -failIfUnchanged (disch := transfer_discharger) only [$args,*] at $hStx:term))
  let mut changed := false
  for h in hs, name in names do
    if (← getUnsolvedGoals).isEmpty then return true
    changed := (← forwardHyp hf h name strict) || changed
  return changed

/-- `transfer hf`, for `hf : MeasurePreserving f P' P`, rewrites the goal with every `@[transfer]`
lemma instantiated at `hf`: the law of `X` under `P` becomes the law of `fun ω ↦ X (f ω)` under
`P'`, and likewise for events, integrals, independence and conditional laws. Side conditions, which
are measurability statements, are discharged by `assumption`, `fun_prop` and `measurability`. The
goal is then closed by `assumption` if possible. It is an error if the goal mentions the old space
and nothing rewrote it.

* `transfer hf at h₁ h₂` transports hypotheses instead: a fact about the old space becomes the
  corresponding fact about the new one, by the same rewriting or, for a hypothesis nothing
  rewrites, by a `@[transfer_forward]` lemma, under the binders of the hypothesis if it has any.
  It is an error if a named hypothesis mentions the old space and is left as it was.
* `transfer hf at h ⊢` and `transfer hf at *` do both, the goal first: transporting a
  measurability hypothesis destroys the fact the goal's side conditions may need. With `*`, the
  only error is when nothing at all changes.
* `transfer` alone discharges the `transfer` obligation of `extend_space`: it introduces the new
  space, the map and the statement on the new space, transfers the goal and closes it with that
  statement. -/
syntax (name := transferTac) "transfer" (ppSpace colGt term)?
  (Lean.Parser.Tactic.location)? : tactic

elab_rules : tactic
  | `(tactic| transfer $[$hf?]? $[$loc?]?) => withMainContext do
    match hf?, loc? with
    | none, some _ =>
      throwError "transfer: `at` needs the map to transfer along, as in `transfer hf at h`"
    | some hf, some loc =>
      let hfE ← Tactic.elabTerm hf none
      let args ← transferSimpArgs hf
      match expandLocation loc with
      | .wildcard =>
        let hs ← (← getLCtx).foldlM (init := #[]) fun hs d ↦ do
          if d.isImplementationDetail || !(← isProp d.type) then pure hs
          else pure (hs.push d.fvarId)
        let goalChanged ← rewriteGoal args
        let hypsChanged ← transferHyps args hfE hs (strict := false)
        closeByAssumption
        unless goalChanged || hypsChanged do
          throwError "transfer: nothing to transfer"
      | .targets hyps type =>
        let hs ← hyps.mapM getFVarId
        let goalChanged ← if type then rewriteGoal args else pure false
        discard <| transferHyps args hfE hs (strict := true)
        if type then
          closeByAssumption
          checkGoalTransferred hfE goalChanged
    | some hf, none =>
      let hfE ← Tactic.elabTerm hf none
      transferGoal (← transferSimpArgs hf) hfE
    | none, none =>
      let (g, hf, h) ← introTransferObligation (← getMainGoal)
      replaceMainGoal [g]
      withMainContext do
        let args ← transferSimpArgs (← Term.exprToSyntax (.fvar hf))
        -- The statement on the new space is simplified too, so that both sides are normalized
        -- the same way: `simp` turns `a = a` into `True` on its own, for instance.
        let hName ← h.getUserName
        let hStx ← Term.exprToSyntax (.fvar h)
        evalTactic (← `(tactic|
          simp -failIfUnchanged (disch := transfer_discharger) only [$args,*] at $hStx:term ⊢))
        if (← getUnsolvedGoals).isEmpty then return
        let g ← getMainGoal
        g.withContext do
          -- `simp at h` replaces `h` by a new hypothesis of the same name.
          let some hDecl := (← getLCtx).findFromUserName? hName
            | throwError "transfer: could not close the goal after transferring it:{indentExpr
              (← g.getType)}"
          unless ← isDefEq (← g.getType) hDecl.type do
            throwError "transfer: could not close the goal after transferring it:{indentExpr
              (← g.getType)}\nwith the statement on the new space:{indentExpr hDecl.type}"
          g.assign hDecl.toExpr
        replaceMainGoal []

end RDo.Tactic

end
