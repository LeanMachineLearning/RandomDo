/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDo.Monad.Program
public meta import Lean.Elab.Tactic.Basic

/-!
# Certificates for existing polymorphic `rdo` definitions

`attribute [rdo_program] foo` keeps `foo` unchanged and generates:

* `foo.program`: the definition interpreted in `RDo.Program`, with sampler primitives recorded;
* `foo.sample_bridge` and `foo.measure_bridge`: equalities with the original interpretations;
* `foo.valid` and `foo.certified`: a compositional measurability certificate;
* `foo.law`: the original sampler's pushforward equals the original measure interpretation.

For example, if `sumDraws coin n` is polymorphic in its measurable-space monad, the attribute
generates `sumDraws.law coin n : (sumDraws coin n).law = sumDraws coin.law n`.
This follows from `RDo.Program.Certified.law`, the universal theorem about certified programs.

`rdo_valid` constructs compositional validity certificates for recorded program families.
It recognizes returns, primitive samplers, binds, measurable branches, and reparameterization.
Definitions are unfolded as needed, and existing certificates can be supplied as hypotheses.

The attribute currently expects leading `{m} [MeasurableSpaceMonad m]` parameters and an
independent universe parameter for the monad's output. Primitive arguments can be samplers
or one-argument sampler families with a fixed result type. For each family, the generated
certificate and law theorem take an additional joint-measurability hypothesis. Automatic
induction uses the last explicit `Nat` argument. General recursion and loops are not yet
handled automatically; unsupported constructs or unresolved measurability obligations fail.
-/

public meta section

open Lean Meta Elab Tactic

namespace RDo.Tactic

/-- Inspect a program family, unfolding its head while preserving the program constructors. -/
def programBody {α : Type} (p : Expr) (k : Expr → Expr → MetaM α) : MetaM α := do
  let p ← etaExpand p
  lambdaBoundedTelescope p 1 fun cs body ↦ do
    let body ← withTransparency .default <| whnfHeadPred body fun e ↦
      return !e.isAppOf ``Program.pure && !e.isAppOf ``Program.sample &&
        !e.isAppOf ``Program.bind && !e.isAppOf ``ite
    k cs[0]! body

/-- Construct the structural part of a program certificate, leaving analytic side conditions. -/
partial def programValidCore (g : MVarId) : MetaM (List MVarId) := g.withContext do
  if ← g.assumptionCore then return []
  let target ← instantiateMVars (← g.getType)
  unless target.isAppOf ``Program.Valid do return [g]
  let rule ← programBody target.appArg! fun c body ↦ do
    if body.isAppOf ``Program.pure then return some ``Program.Valid.pure
    if body.isAppOf ``Program.sample then return some ``Program.Valid.sample
    if body.isAppOf ``Program.bind then return some ``Program.Valid.bind
    if body.isAppOf ``ite then return some ``Program.Valid.ite
    if !body.containsFVar c.fvarId! && !(← inferType c).isConstOf ``PUnit then
      return some ``Program.Valid.const
    if body.isApp && !body.appFn!.containsFVar c.fvarId!
        && body.appArg!.containsFVar c.fvarId! && body.appArg! != c then
      return some ``Program.Valid.comp
    return none
  let some rule := rule | return [g]
  let gs ← g.applyConst rule
  return (← gs.mapM programValidCore).flatten

/-- Reuse a joint-measurability hypothesis after changing the family parameter and source state.
Keeping these two arguments paired avoids asking `fun_prop` to prove separate measurability. -/
def programSampleFamilyMeasurable (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let target ← instantiateMVars (← g.getType)
  unless target.isAppOf ``Measurable do return [g]
  lambdaBoundedTelescope (← etaExpand target.appArg!) 1 fun xs body ↦ do
    let body ← whnfHeadPred body fun e ↦ return !e.isAppOf ``RandomM.sample
    unless body.isAppOfArity ``RandomM.sample 7 do return [g]
    let sampler := body.appFn!.appArg!
    unless sampler.isApp && !sampler.appFn!.containsFVar xs[0]!.fvarId! do return [g]
    let family ← withLocalDeclD `a (← inferType sampler.appArg!) fun a ↦ do
      mkLambdaFVars #[a] (← mkAppM ``RandomM.sample #[mkApp sampler.appFn! a])
    let condition ← mkAppM ``Measurable #[← mkAppM ``Function.uncurry #[family]]
    for decl in ← getLCtx do
      if ← isDefEq decl.type condition then
        let change ← mkLambdaFVars xs (← mkAppM ``Prod.mk #[sampler.appArg!, body.appArg!])
        let hg ← mkFreshExprMVar (← mkAppM ``Measurable #[change])
        g.assign (← mkAppM ``Measurable.comp #[decl.toExpr, hg])
        return [hg.mvarId!]
    return [g]

/-- Prove the compositional validity of a recorded program family. Unproved measurability
conditions and unsupported constructs are left as goals. -/
syntax (name := rdoValidTac) "rdo_valid" : tactic

/-- Elaborate a validity proof by composing program certificates and proving measurability. -/
@[tactic rdoValidTac]
def elabRdoValid : Tactic := fun _ ↦ do
  liftMetaTactic fun g ↦ do
    return (← (← programValidCore g).mapM programSampleFamilyMeasurable).flatten
  evalTactic (← `(tactic| all_goals try first | assumption | fun_prop))

/-- Add an exposed mathematical companion definition, without requiring executable code. -/
def addProgramDef (name : Name) (levels : List Name) (args : Array Expr) (body : Expr) :
    TermElabM Expr := do
  let value ← instantiateMVars (← mkLambdaFVars args body)
  addDecl (.defnDecl {
    name, levelParams := levels, type := ← inferType value, value,
    hints := .abbrev, safety := .safe
  }) (forceExpose := true)
  modifyEnv (Lean.addNoncomputable · name)
  enableRealizationsForConst name
  return mkAppN (mkConst name (levels.map Level.param)) args

/-- Add a kernel-checked companion theorem with the same explicit arguments. -/
def addProgramTheorem (name : Name) (levels : List Name) (args : Array Expr) (proof : Expr) :
    TermElabM Expr := do
  Term.synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars (← mkLambdaFVars args proof)
  if value.hasSorry || value.hasMVar then
    throwError "rdo_program: the certificate for {name} has unresolved proof obligations"
  addDecl (.thmDecl { name, levelParams := levels, type := ← inferType value, value })
  return mkAppN (mkConst name (levels.map Level.param)) args

/-- Prove a companion obligation, using induction on the last explicit natural-number argument.
This handles structural counting programs without unrolling a fixed number of draws. -/
def proveProgramObligation (args : Array Expr) (target : Expr) (tac : TSyntax `tactic) :
    TermElabM Expr := Term.withoutErrToSorry do
  let n? ← args.findSomeRevM? fun a ↦ do
    let decl ← a.fvarId!.getDecl
    return if decl.binderInfo.isExplicit && decl.type.isConstOf ``Nat then
      some (mkIdent decl.userName) else none
  let tacticCode ← match n? with
    | none => `(by $tac:tactic)
    | some n =>
      let n ← `(Lean.Parser.Tactic.elimTarget| $n:term)
      `(by induction $n <;> $tac:tactic)
  let proof ← mkFreshExprSyntheticOpaqueMVar target
  -- Fail before Lean abstracts a public proof into an auxiliary theorem: checking `hasSorry`
  -- on the resulting theorem reference would miss an unresolved goal in its body.
  Term.runTactic proof.mvarId! tacticCode .term (report := false)
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  if proof.hasSorry || proof.hasMVar then
    throwError "rdo_program: could not certify this program; an unsupported construct or \
      a measurability obligation remains"
  return proof

/-- Build a recording interpretation, its certificate, bridges to both original interpretations,
and the resulting law theorem for a polymorphic definition. -/
def addProgramCompanions (declName : Name) : TermElabM Unit := do
  let info ← getConstInfo declName
  unless info.hasValue do
    throwError "rdo_program: expected a definition"
  let .forallE _ _ (.forallE _ instType _ _) _ := info.type |
    throwError "rdo_program: expected a leading monad parameter \
      and its MeasurableSpaceMonad instance"
  unless instType.isAppOfArity ``MeasurableSpaceMonad 1 && instType.appArg! == .bvar 0 do
    throwError "rdo_program: expected a leading monad parameter \
      and its MeasurableSpaceMonad instance"
  let [u, .param v] := instType.getAppFn.constLevels! |
    throwError "rdo_program: the monad's output universe must be a universe parameter"
  if (.param v : Level).occurs u then
    throwError "rdo_program: the monad's output universe must be independent of its input universe"
  let mut wName := `rdo_w
  while info.levelParams.contains wName do
    wName := wName.appendAfter "_"
  let w := Level.param wName
  let levels := info.levelParams.filter (· != v) ++ [wName]
  let root (m : Expr) (out : Level) : MetaM Expr := do
    let inst ← synthInstance (mkApp (mkConst ``MeasurableSpaceMonad [u, out]) m)
    return mkApp2 (mkConst declName (info.levelParams.map fun n ↦
      if n == v then out else .param n)) m inst
  withLocalDecl `Ω .implicit (mkSort (.succ w)) fun Ω ↦ do
  withLocalDecl `instΩ .instImplicit (mkApp (mkConst ``MeasurableSpace [w]) Ω) fun mΩ ↦ do
  withLocalDecl `P .implicit (mkApp2 (mkConst ``MeasureTheory.Measure [w]) Ω mΩ) fun P ↦ do
  withLocalDecl `prob .instImplicit
      (mkApp3 (mkConst ``MeasureTheory.IsProbabilityMeasure [w]) Ω mΩ P) fun prob ↦ do
    let samplerM := mkApp3 (mkConst ``RandomM [u, w]) Ω mΩ P
    let programM := mkApp3 (mkConst ``Program [u, w]) Ω mΩ P
    let samplerRoot ← root samplerM (Level.max u w).normalize
    let programRoot ← root programM (Level.max (.succ u) w).normalize
    let measureRoot ← root (mkConst ``MeasureTheory.Measure [u]) u
    forallTelescope (← inferType samplerRoot) fun args resultType ↦ do
      unless resultType.isAppOfArity ``RandomM 5 do
        throwError "rdo_program: expected the definition to return m α"
      let mut programArgs := #[]
      let mut measureArgs := #[]
      let mut familyConditions : Array (Name × Expr) := #[]
      for a in args do
        let ty ← inferType a
        if ty.isAppOfArity ``RandomM 5 then
          programArgs := programArgs.push (← mkAppM ``Program.sample #[a])
          measureArgs := measureArgs.push (← mkAppM ``RandomM.law #[a])
        else if ty.isForall then
          let lifted? ← forallBoundedTelescope ty (some 1) fun xs result ↦ do
            unless result.isAppOfArity ``RandomM 5 do return none
            if result.containsFVar xs[0]!.fvarId! then
              throwError "rdo_program: dependent result types in primitive families are unsupported"
            let value := mkApp a xs[0]!
            let program ← mkLambdaFVars xs (← mkAppM ``Program.sample #[value])
            let measure ← mkLambdaFVars xs (← mkAppM ``RandomM.law #[value])
            let samples ← mkLambdaFVars xs (← mkAppM ``RandomM.sample #[value])
            let condition ← mkAppM ``Measurable #[← mkAppM ``Function.uncurry #[samples]]
            return some (program, measure, condition)
          if let some (program, measure, condition) := lifted? then
            programArgs := programArgs.push program
            measureArgs := measureArgs.push measure
            let name := (← a.fvarId!.getDecl).userName.appendAfter "_measurable"
            familyConditions := familyConditions.push (name, condition)
          else
            programArgs := programArgs.push a
            measureArgs := measureArgs.push a
        else
          programArgs := programArgs.push a
          measureArgs := measureArgs.push a
      let recorded := mkAppN programRoot programArgs
      let sampled := mkAppN samplerRoot args
      let measured := mkAppN measureRoot measureArgs
      check recorded
      check measured
      let allArgs := #[Ω, mΩ, P, prob] ++ args
      let program ← addProgramDef (declName ++ `program) levels allArgs recorded
      let decl := mkIdent declName
      let programDecl := mkIdent (declName ++ `program)
      let bridgeTac ← `(tactic| simp_all only [$programDecl:ident, $decl:ident,
        MeasurableSpacePure.mPure, MeasurableSpaceBind.mBind,
        Program.sampleSemantics, Program.measureSemantics, apply_ite])
      let sampleEq ← mkEq (← mkAppM ``Program.sampleSemantics #[program]) sampled
      let sampleBridge ← addProgramTheorem (declName ++ `sample_bridge) levels allArgs
        (← proveProgramObligation args sampleEq bridgeTac)
      let measureEq ← mkEq (← mkAppM ``Program.measureSemantics #[program]) measured
      let measureBridge ← addProgramTheorem (declName ++ `measure_bridge) levels allArgs
        (← proveProgramObligation args measureEq bridgeTac)
      withLocalDeclsD (familyConditions.map fun (name, ty) ↦ (name, fun _ ↦ pure ty)) fun hs ↦ do
        let certArgs := allArgs ++ hs
        let family ← withLocalDeclD `unit (mkConst ``PUnit [.succ u]) fun unit ↦
          mkLambdaFVars #[unit] recorded
        let validType ← mkAppM ``Program.Valid #[family]
        let validProof ← proveProgramObligation args validType (← `(tactic| rdo_valid))
        let valid ← addProgramTheorem (declName ++ `valid) levels certArgs validProof
        let certified ← addProgramDef (declName ++ `certified) levels certArgs
          (← mkAppM ``Program.Certified.mk #[program, valid])
        let law ← mkAppM ``Program.Certified.law_of_bridge
          #[certified, sampled, measured, sampleBridge, measureBridge]
        discard <| addProgramTheorem (declName ++ `law) levels certArgs law

/-- Generate a certified representation and sampler–measure bridges for a polymorphic program.
The original definition is unchanged. Primitive sampler arguments are interpreted by their laws.
Primitive families add joint-measurability hypotheses to the generated certificate and law.
The first version supports leading `{m} [MeasurableSpaceMonad m]` parameters, an independent
output-universe parameter, and structural induction on the last explicit `Nat` argument. -/
initialize registerBuiltinAttribute {
  name := `rdo_program
  descr := "generate a certified program representation, interpretation bridges, and a law theorem"
  applicationTime := .afterCompilation
  add := fun declName _stx kind ↦ do
    unless kind == AttributeKind.global do
      throwError "rdo_program must be a global attribute"
    let env ← getEnv
    try
      (addProgramCompanions declName).run'.run'
    catch e =>
      setEnv env
      throw e
}

end RDo.Tactic
