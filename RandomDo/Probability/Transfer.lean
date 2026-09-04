/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
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
nothing rewrites, by a `@[transfer_forward]` lemma: this pulls a fact about the old space back to
the new one. `transfer` alone is for the obligation left by `extend_space`: it introduces the new
space, the map and the statement on the new space, transfers the goal, and closes it with that
statement.
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

/-- The discharger for the side conditions of `@[transfer]` lemmas: `assumption`, then `fun_prop`
for the measurability of a function and `measurability` for that of a set. A maximum recursion
depth error inside `measurability`, which happens on unprovable goals, is turned into a plain
failure so that it only makes the rewrite fail. -/
syntax (name := transferDischarger) "transfer_discharger" : tactic

elab_rules : tactic
  | `(tactic| transfer_discharger) => withMainContext do
    let funProps : Array Name := #[``Measurable, ``AEMeasurable,
      `MeasureTheory.AEStronglyMeasurable, `MeasureTheory.StronglyMeasurable]
    let head := (← getMainTarget).getAppFn.constName?
    let tac ← if head.any funProps.contains then `(tactic| first | assumption | fun_prop)
      else `(tactic| first | assumption | measurability)
    tryCatchRuntimeEx (evalTactic tac) fun e ↦
      throwError "transfer_discharger: {e.toMessageData}"

/-- The `@[transfer]` lemmas instantiated at `hf`, as `simp` arguments, together with the lemmas
pushing a preimage through set operations, which put the transferred events in the same form as
`extend_space`. -/
def transferSimpArgs (hf : Term) : CoreM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) := do
  let args ← (← labelled `transfer).mapM fun n ↦
    `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident $hf)
  let extra ← #[``Set.preimage_ofPred_eq, ``Set.preimage_inter, ``Set.preimage_union,
    ``Set.preimage_compl, ``Set.preimage_sdiff].mapM fun n ↦
      `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  return args ++ extra

/-- Try to close the goal `g` with `tac`, returning its proof. The state is restored on failure,
and a runtime error such as a maximum recursion depth counts as a failure. -/
def tryTactic? (g : MVarId) (tac : Syntax) : TacticM (Option Expr) := do
  let s ← saveState
  tryCatchRuntimeEx
    (do
      let gs ← Tactic.run g (evalTactic tac)
      if gs.isEmpty then return some (← instantiateMVars (.mvar g))
      s.restore
      return none)
    (fun _ ↦ do
      s.restore
      return none)

/-- Transport the hypothesis `h` forward along `hf` with a `@[transfer_forward]` lemma, as
`lemma h hf side…`, the side conditions being discharged by `transfer_discharger`. Returns the
statement and proof of the transported hypothesis. -/
def transferForward? (h hf : Expr) : TacticM (Option (Expr × Expr)) := do
  let hStx ← Term.exprToSyntax h
  let hfStx ← Term.exprToSyntax hf
  for n in ← labelled `transfer_forward do
    let s ← saveState
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
        pure (some (concl, pf)))
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

/-- Transfer the goal along `hf`: rewrite it with the `@[transfer]` lemmas, then close it by
`assumption` if possible. -/
def transferGoal (hfStx : Term) : TacticM Unit := do
  let args ← transferSimpArgs hfStx
  evalTactic (← `(tactic| simp -failIfUnchanged (disch := transfer_discharger) only [$args,*]))
  unless (← getUnsolvedGoals).isEmpty do
    evalTactic (← `(tactic| try assumption))

/-- Transfer the hypotheses `hs` along `hf`: rewrite each with the `@[transfer]` lemmas, then
replace each one that did not change by its forward transport by a `@[transfer_forward]` lemma.
All the rewriting comes first, since a forward transport destroys the measurability facts the
rewriting may need. -/
def transferHyps (hfStx : Term) (hf : Expr) (hs : Array FVarId) : TacticM Unit := do
  let args ← transferSimpArgs hfStx
  for h in hs do
    let hStx ← withMainContext do Term.exprToSyntax (.fvar h)
    evalTactic (← `(tactic|
      simp -failIfUnchanged (disch := transfer_discharger) only [$args,*] at $hStx:term))
  for h in hs do
    withMainContext do
      -- `simp` replaces the hypothesis when it rewrites it; otherwise it is still there.
      let some d := (← getLCtx).find? h | return
      let some (ty, pf) ← transferForward? d.toExpr hf | return
      let g ← (← getMainGoal).assert d.userName ty pf
      let (_, g) ← g.intro1P
      replaceMainGoal [← g.tryClear h]

/-- `transfer hf`, for `hf : MeasurePreserving f P' P`, rewrites the goal with every `@[transfer]`
lemma instantiated at `hf`: the law of `X` under `P` becomes the law of `fun ω ↦ X (f ω)` under
`P'`, and likewise for events, integrals, independence and conditional laws. Side conditions, which
are measurability statements, are discharged by `assumption`, `fun_prop` and `measurability`. The
goal is then closed by `assumption` if possible.

* `transfer hf at h₁ h₂` transports hypotheses instead: a fact about the old space becomes the
  corresponding fact about the new one, by the same rewriting or, for a hypothesis nothing
  rewrites, by a `@[transfer_forward]` lemma.
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
      match expandLocation loc with
      | .wildcard =>
        let hs ← withMainContext do
          (← getLCtx).foldlM (init := #[]) fun hs d ↦ do
            if d.isImplementationDetail || !(← isProp d.type) then pure hs
            else pure (hs.push d.fvarId)
        transferHyps hf hfE hs
        transferGoal hf
      | .targets hyps type =>
        transferHyps hf hfE (← withMainContext do hyps.mapM getFVarId)
        if type then transferGoal hf
    | some hf, none => transferGoal hf
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
