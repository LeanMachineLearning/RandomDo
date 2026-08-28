/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import RandomDo.Tactic.Lemmas
public meta import Lean.Elab.Tactic.Basic

/-!
# The `is_markov` tactic

This file implements `is_markov`, which proves that an `rdo` program is a Markov kernel or, for a
program taking no parameter, a probability measure.

The tactic reads a program as a tree of `rdo` constructs. At each node it applies a lemma of
`LeanMachineLearning.RDo.Tactic.Lemmas` propagating the Markov property through that construct, and
recurses into the `IsMarkov` hypotheses that lemma leaves behind. The rest — the measurability side
conditions the lemmas ask for, and the leaves the tactic was not taught about — is handed back to
the user, after a last attempt by `fun_prop` and `assumption`. Definitions heading the program are
looked through along the way, so `unfold` is not needed before `is_markov`.
-/

public meta section

open Lean Lean.Meta Lean.Elab.Tactic
open MeasureTheory

namespace RDo.Tactic

initialize registerTraceClass `is_markov

/-- Which `rdo` construct a program is made of, as far as the tactic is concerned. -/
inductive Shape
  /-- `return e`, elaborated to `MeasurableSpacePure.mPure e`. -/
  | mPure
  /-- `let x ← p; q`, elaborated to `MeasurableSpaceBind.mBind p q`. -/
  | mBind
  /-- `fun c ↦ κ (g c)`: a family `κ` that does not mention the parameter, read through a
  reparametrisation `g`. -/
  | comp
  /-- `fun c ↦ if p c then κ c else η c`: a if-then-else over two families of measures. -/
  | ite
  /-- `fun c ↦ if h : p c then κ c h else η c h`: a dependent if-then-else. The condition and the
  two branches are carried along, abstracted over the parameter, because `apply` cannot recover
  them: the branches take the proof, whereas the lemma indexes them by a subtype. -/
  | dite (p tb fb : Expr)
  /-- `for a in as rdo body`: a `for` loop over a collection. The two lemmas to try are carried
  along, one for a fixed collection and one for a collection read off the parameter, so that the
  three collections `rdo` supports share a single branch below. -/
  | forIn (fixed varying : Name)
  /-- `Break.runK r (fun _ ↦ κ) η`: the case analysis an `rdo` block performs after a loop that
  returns early. -/
  | breakRunK
  /-- `fun _ ↦ μ`: a family that does not look at its parameter at all. -/
  | const
  /-- Anything else: a fixed distribution, a program the tactic was not taught about. These are
  the leaves of the recursion. -/
  | leaf
  --deriving Inhabited

instance : ToString Shape where
  toString
    | .mPure => "mPure"
    | .mBind => "mBind"
    | .comp => "comp"
    | .ite => "ite"
    | .dite .. => "dite"
    | .forIn .. => "forIn"
    | .breakRunK => "breakRunK"
    | .const => "const"
    | .leaf => "leaf"

/-- `whnfR`, but stopping as soon as the head is `Break.runK`. That constant is an `abbrev`, hence
reducible, so plain `whnfR` unfolds it into its matcher and the shape below is never recognised. -/
def whnfRStopAtBreakRunK (e : Expr) : MetaM Expr :=
  withReducible <| whnfHeadPred e fun e ↦ return !e.isAppOf ``Break.runK

/-- Recognise the construct a family of measures `κ : γ → Measure α` is built from. -/
def shapeOf (κ : Expr) : MetaM Shape := do
  let κ ← etaExpand (← whnfR κ)
  lambdaBoundedTelescope κ 1 fun cs body ↦ do
    let c := cs[0]!
    /- `etaExpand` rebuilds `κ` as `fun c ↦ (…) c`, so `body` is a beta-redex even when the
    original program was not an application. Normalising it once here is what makes the tests
    below look at the program itself rather than at that redex. -/
    let body ← whnfRStopAtBreakRunK body
    let head := body.getAppFn
    if head.isConstOf ``MeasurableSpacePure.mPure then
      return .mPure
    else if head.isConstOf ``MeasurableSpaceBind.mBind then
      return .mBind
    else if head.isConstOf ``ite then
      return .ite
    else if head.isConstOf ``dite then
      /- `dite` takes five arguments: the type, the condition, the `Decidable` instance, and the
      two branches. Only the last four matter, abstracted over `c`. -/
      let args := body.getAppArgs
      return .dite (← mkLambdaFVars #[c] args[1]!) (← mkLambdaFVars #[c] args[3]!)
        (← mkLambdaFVars #[c] args[4]!)
    else if head.isConstOf ``MeasurableSpaceForIn.forIn then
      match body.getAppArgs[1]!.getAppFn with
      | .const ``List _ => return .forIn ``IsMarkov.forInList ``IsMarkov.forInList_comp
      | .const ``Array _ => return .forIn ``IsMarkov.forInArray ``IsMarkov.forInArray_comp
      | .const ``Vector _ => return .forIn ``IsMarkov.forInVector ``IsMarkov.forInVector_comp
      | _ => return .leaf
    else if head.isConstOf ``Break.runK then
      return .breakRunK
    else if body.isApp
      && !body.appFn!.containsFVar c.fvarId!
      && body.appArg!.containsFVar c.fvarId!
      && body.appArg! != c then
      /- The last conjunct rules out `body = κ c`, which is what `etaExpand` produces out of a
      program that was not a lambda to begin with. Without it, `IsMarkov ⇑κ` would be read as a
      reparametrisation of itself by the identity, and the recursion below would never end. -/
      return .comp
    else if !body.containsFVar c.fvarId! then
      return .const
    else
      return .leaf

/-- Try to close a leaf goal `IsMarkov κ`, either by instance synthesis or from a hypothesis of the
local context. On failure the goal is handed back unchanged. -/
def closeLeaf (g : MVarId) : MetaM (List MVarId) := do
  if let .some proof ← trySynthInstance (← g.getType) then
    trace[is_markov] "closed by instance synthesis"
    g.assign proof
    return []
  if ← g.assumptionCore then
    trace[is_markov] "closed by a hypothesis of the local context"
    return []
  /- A distribution whose parameters are read off the parameter of the kernel is not an instance.
  Handing back its measurability side conditions stops the unfolding below from diving into the
  definition of the distribution itself. -/
  if let some gs ← observing? (g.applyConst ``IsMarkov.gaussianReal) then
    trace[is_markov] "`gaussianReal` leaf: handing back the measurability of its parameters"
    return gs
  return [g]

/-- The constant heading the body of `κ`, when it is a definition the tactic could look through. -/
def programHeadDef? (κ : Expr) : MetaM (Option Name) := do
  let κ ← etaExpand (← whnfR κ)
  lambdaBoundedTelescope κ 1 fun _ body ↦ do
    let .const n _ := (← whnfR body).getAppFn | return none
    let some info := (← getEnv).find? n | return none
    return if info.hasValue then some n else none

/-- Default number of definitions `is_markov` looks through before giving up. -/
def defaultUnfoldFuel : Nat := 8

/-- Look through the definitions heading the program, until one of the constructs the tactic
knows shows up. This is what makes `unfold` unnecessary before `is_markov`. -/
partial def unfoldToKnownShape (target : Expr) (fuel : Nat) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  unless target.isAppOfArity ``IsMarkov 5 do return none
  let some n ← programHeadDef? target.appArg! | return none
  let target' ← deltaExpand target (· == n)
  if target' == target then return none
  match ← shapeOf target'.appArg! with
  | .leaf => unfoldToKnownShape target' (fuel - 1)
  | _ => return some target'

/-- Check if a goal depends on the free variables `vars`, and if so, revert them. Otherwise, try to
clear them. -/
def abstractLoopVars (vars : Array FVarId) (g : MVarId) : MetaM MVarId := do
  let target ← instantiateMVars (← g.getType)
  if vars.any target.containsFVar then
    return (← g.revert vars).2
  else
    g.tryClearMany vars

/-- Turn a goal `IsMarkov κ` into the list of goals the user is left with. -/
partial def isMarkovCore (g : MVarId) (fuel : Nat) : MetaM (List MVarId) := g.withContext do
  let target ← instantiateMVars (← g.getType)
  -- `IsMarkov` takes five arguments: `γ`, `α`, their `MeasurableSpace` instances, and `κ`.
  unless target.isAppOfArity ``IsMarkov 5 do
    trace[is_markov] "not an `IsMarkov` goal, handed back: {target}"
    return [g]
  let shape ← shapeOf target.appArg!
  withTraceNode `is_markov
      (fun _ ↦ return m!"{shape}: {target.appArg!}") do
    match shape with
    | .mPure =>
      -- `return e`: one lemma, and the measurability of `e` is left to the user.
      g.applyConst ``IsMarkov.mPure_comp
    | .mBind =>
      -- `let x ← p; q`: two hypotheses, both `IsMarkov` goals, so we recurse into both.
      let mut goals := []
      for g' in ← g.applyConst ``IsMarkov.mBind do
        goals := goals ++ (← isMarkovCore g' fuel)
      return goals
    | .comp =>
      /- `fun c ↦ κ (g c)`: two hypotheses, one `IsMarkov` goal and one measurability goal, so we
      recurse into the first and leave the second to the user. -/
      let gs ← g.applyConst ``IsMarkov.comp
      match gs with
      | [g_is_markov, g_measurable] =>
        return (← isMarkovCore g_is_markov fuel) ++ [g_measurable]
      | _ =>
        throwError "is_markov: expected two goals after the `comp` step, got {gs.length}"
    | .ite =>
      /- `if p c then κ c else η c`: three hypotheses, one measurability goal and two `IsMarkov`
      goals, so we leave the first to the user and recurse into the last two -/
      let gs ← g.applyConst ``IsMarkov.ite
      match gs with
      | hd :: tl =>
        let mut goals := [hd]
        for g' in tl do
          goals := goals ++ (← isMarkovCore g' fuel)
        return goals
      | _ =>
        throwError "is_markov: expected at least one goal after the `ite` step, got {gs.length}"
    | .dite p tb fb =>
      /- `if h : p c then tb c h else fb c h`. The lemma indexes its branches by the subtypes
      `{c // p c}` and `{c // ¬ p c}`, so we reassociate the two branches into that form here
      (`κ x = tb x.1 x.2`) and build the application ourselves. -/
      let dom := (← inferType p).bindingDomain!
      let notP ← withLocalDeclD `c dom fun c ↦ do
        mkLambdaFVars #[c] (← mkAppM ``Not #[(p.beta #[c])])
      let bundle (branch pred : Expr) : MetaM Expr := do
        let subtype ← mkAppM ``Subtype #[pred]
        withLocalDeclD `x subtype fun x ↦ do
          let v ← mkAppM ``Subtype.val #[x]
          let h ← mkAppM ``Subtype.property #[x]
          mkLambdaFVars #[x] (mkApp2 branch v h).headBeta
      let hp ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Measurable #[p])
      let hκ ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``IsMarkov #[← bundle tb p])
      let hη ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``IsMarkov #[← bundle fb notP])
      let proof ← mkAppM ``IsMarkov.dite #[hp, hκ, hη]
      unless ← isDefEq (← g.getType) (← inferType proof) do
        throwError "is_markov: the `dite` step does not match the goal {indentExpr (← g.getType)}"
      g.assign proof
      return (← isMarkovCore hκ.mvarId! fuel) ++ (← isMarkovCore hη.mvarId! fuel) ++ [hp.mvarId!]
    | .forIn fixed varying =>
      if let some gs ← observing? (g.applyConst fixed) then
        /- Fixed collection: a measurability goal for the initial value, and
        `∀ a ∈ as, IsMarkov fun p ↦ body p.1 a p.2` for the body. Walking through the body needs
        the element in the local context, so it is introduced, then abstracted away again from
        whatever the recursion did not close. -/
        match gs with
        | [g_measurable, g_is_markov] =>
          let (i, g_body) ← g_is_markov.intro1P
          let (h, g_body) ← g_body.intro1P
          return (← (← isMarkovCore g_body fuel).mapM (abstractLoopVars #[i, h])) ++ [g_measurable]
        | _ =>
          throwError "is_markov: expected two goals after the `forIn` step, got {gs.length}"
      else if let some gs ← observing? (g.applyConst varying) then
        /- Collection read off the parameter: the body is Markovian jointly in the element, so
        there is no element to introduce. The measurability goals are left to the user. -/
        let mut goals := []
        let mut side := []
        for g' in gs do
          if (← instantiateMVars (← g'.getType)).isAppOfArity ``IsMarkov 5 then
            goals := goals ++ (← isMarkovCore g' fuel)
          else
            side := side ++ [g']
        return goals ++ side
      else
        trace[is_markov] "neither `forIn` lemma applies, handed back"
        return [g]
    | .breakRunK =>
      let gs ← g.applyConst ``IsMarkov.breakRunK
      match gs with
      | hd :: tl =>
        let mut goals := [hd]
        for g' in tl do
          goals := goals ++ (← isMarkovCore g' fuel)
        return goals
      | _ =>
        throwError "is_markov: expected at least one goal after the `breakRunK` step, \
          got {gs.length}"
    | .leaf | .const =>
      /- A leaf: either something already known — a fixed distribution, a hypothesis, a program
      with its own `IsMarkov` instance — or a definition still to be looked through, or a constant
      family — a probability measure. The tactic tries to close the goal, and if it cannot, it
      looks through the definition, or ultimately hands the goal back to the user. -/
      let leftover ← closeLeaf g
      -- `closeLeaf` may have proved the goal outright, or reduced it to side conditions.
      if ← g.isAssigned then return leftover
      /- The goal was not closed, so we try to unfold names in the head of the program until we
      reach a known shape. If that fails, we leave the goal to the user. -/
      match ← unfoldToKnownShape (← instantiateMVars (← g.getType)) fuel with
      | some target =>
        trace[is_markov] "unfolded the head definition to: {target.appArg!}"
        isMarkovCore (← g.change target) (fuel - 1)
      | none =>
        /- Nothing worked. If the family is constant, we change the goal into
        `IsProbabilityMeasure` and let the user prove it. -/
        if shape matches .const then
          trace[is_markov] "constant family, handed back as `IsProbabilityMeasure`"
          g.applyConst ``IsMarkov.const
        else
          trace[is_markov] "handed back to the user"
          return leftover

/-- Hand a goal back only once: a goal repeating one already in the list is proved by sharing its
proof. Every goal `is_markov` produces lives in the local context of the goal it started from —
that is what `abstractLoopVar` is for — so two goals with the same statement are the same goal. -/
def shareDuplicateGoals (gs : List MVarId) : MetaM (List MVarId) := do
  let mut kept : Array MVarId := #[]
  for g in gs do
    let t ← instantiateMVars (← g.getType)
    if let some k ← kept.findM? fun k ↦ return t == (← instantiateMVars (← k.getType)) then
      g.assign (mkMVar k)
    else
      kept := kept.push g
  return kept.toList

/-- A program with no parameter denotes a probability measure as soon as the constant family it
defines is a Markov kernel. -/
lemma _root_.isProbabilityMeasure_of_isMarkov {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (h : IsMarkov fun _ : Unit ↦ μ) : IsProbabilityMeasure μ :=
  h.isProbabilityMeasure ()

/-- Bring a goal of the form `IsProbabilityMeasure μ` into the form `IsMarkov fun _ : Unit ↦ μ`, so
that `isMarkovCore` can be applied. -/
def toIsMarkovGoal (g : MVarId) : MetaM MVarId := do
  let target ← instantiateMVars (← g.getType)
  unless target.isAppOfArity ``IsProbabilityMeasure 3 do
    return g
  match ← g.applyConst ``isProbabilityMeasure_of_isMarkov with
  | [g'] => return g'
  | gs =>
    throwError "is_markov: expected one goal after the `IsProbabilityMeasure` step, \
      got {gs.length}"

/-- Run several closing tactics on a goal, and keep the goal unchanged if they all fail. -/
def tryClosingTactics (g : MVarId) : TacticM (List MVarId) := do
  let tac ← `(tactic| try first | fun_prop (disch := measurability))
  Lean.Elab.Tactic.run g (evalTactic tac)

/-- `is_markov` proves that an `rdo` program in the `MeasurableSpaceMonad` is a Markov kernel
(goal `RDo.IsMarkov prog`) or, for a program with no parameter, a probability measure
(goal `IsProbabilityMeasure prog`).

It walks through the structure of the program, and finishes by running closing tactics on each side
condition it produced. If the tactic cannot close a goal, it is left to the user to prove it. It
automatically looks through definitions, so `unfold` is not needed before `is_markov`. The number
of definitions it looks through is limited to `8` by default but can be changed by passing a `fuel`
argument:

* `is_markov (fuel := n)` looks through up to `n` definitions.

Example:

```
noncomputable def prog : Measure ℝ := rdo
  let x ← gaussianReal 0 1
  let y ← gaussianReal 0 1
  return x + y

example : IsProbabilityMeasure prog := by
  is_markov
```

Setting `set_option trace.is_markov true` prints the tree of constructs the tactic walked
through, and how each leaf was closed. -/
syntax (name := isMarkovTac) "is_markov" (" (" &"fuel" " := " num ")")? : tactic

elab_rules : tactic
  | `(tactic| is_markov $[(fuel := $fuel?)]?) => classical do
    let fuel := (fuel?.map (·.getNat)).getD defaultUnfoldFuel
    let goals ← isMarkovCore (← toIsMarkovGoal (← getMainGoal)) fuel
    let mut remaining := []
    for g in goals do
      remaining := remaining ++ (← tryClosingTactics g)
    replaceMainGoal (← shareDuplicateGoals remaining)

end RDo.Tactic

end
