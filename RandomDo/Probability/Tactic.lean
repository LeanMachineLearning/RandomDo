/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import RandomDo.Probability.Trace
public import RandomDo.Tactic.Elab
public meta import Lean.Elab.Tactic.Basic

/-!
# The `rdo_trace` and `rdo_peel` tactics

`rdo_trace` builds the trace of an `rdo` program: it walks the same program tree that `is_markov`
walks, applying at each node the combinator of `RandomDo.Probability.Trace` for that construct, and
adds `h : RDo.HasTrace prog P out` to the context with `P` and `out` computed. The measurability
and `IsMarkov` obligations the combinators leave behind become goals, and are attacked with
`is_markov` and `fun_prop`.

`rdo_peel` then reads the probabilistic statements off such a hypothesis: the law of the first
draw, the conditional law of each later draw given the draws before it, the law of the program's
result — and, for every draw whose kernel does not depend on the draws before it, an
unconditional law together with an independence statement.

Both keep the local context readable: an `rdo` program's text ends up inside its trace kernel, and
every statement a peeled trace adds mentions the trace measure built from those kernels. Anything
too wide to print is given a local definition of its own — `κ₁`, `κ₂`, … for the kernels, `P` for
the trace measure — so the hypotheses stay one line each.

-/

public meta section

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic
open MeasureTheory ProbabilityTheory

namespace RDo.Tactic

initialize registerTraceClass `rdo_trace

/-! ## Small expression utilities -/

/-- Beta-reduce, and reduce `(a, b).1` and `(a, b).2`. This is what turns the continuation of a
`mBind`, which the tactic builds by substituting a pair for the parameter, back into a readable
term. -/
partial def betaProj (e : Expr) : MetaM Expr := do
  let step (e : Expr) : Expr :=
    let e := e.headBeta
    if e.isAppOfArity ``Prod.fst 3 then
      let p := e.appArg!
      if p.isAppOfArity ``Prod.mk 4 then p.appFn!.appArg! else e
    else if e.isAppOfArity ``Prod.snd 3 then
      let p := e.appArg!
      if p.isAppOfArity ``Prod.mk 4 then p.appArg! else e
    else if e.isAppOfArity ``DFunLike.coe 6 then
      -- `(Kernel.const γ ν) a = ν` and `(markovKernel prog h) a = prog a`, both by `rfl`.
      let as := e.getAppArgs
      let f := as[4]!
      if f.isAppOf ``ProbabilityTheory.Kernel.const then f.appArg!
      else if f.isAppOfArity ``markovKernel 6 then mkApp f.appFn!.appArg! as[5]!
      else e
    else e
  let e ← Meta.transform e (post := fun e ↦ return .done (step e))
  Meta.transform e (post := fun e ↦ return .done (step e))

/-! ### Keeping the context readable

An `rdo` program's own text ends up inside its trace kernel, and every hypothesis a peeled trace
adds mentions the trace measure built from those kernels. Printed in full, once per hypothesis,
that is unreadable. So the kernels that are big are given local definitions of their own, `κ₁`,
`κ₂`, …, and the trace measure a local definition `P`; the hypotheses then mention only those.
-/

/-- Wider than this, printed, and a term is pulled out into a local definition rather than shown in
every hypothesis that mentions it. Printed width is the right measure here rather than the number
of subterms: a kernel's implicit type arguments are large but are not shown. -/
def abstractionWidth : Nat := 60

/-- Is `e` too wide to print in every hypothesis? -/
def tooWide (e : Expr) : MetaM Bool := do
  return (← ppExpr e).pretty.length > abstractionWidth

/-- Unfold a head that is a local `let` variable — the ones introduced below to keep the context
readable — so that the shape of a kernel stays visible to the tactic. -/
partial def unfoldLetHead (e : Expr) : MetaM Expr := do
  let .fvar fid := e | return e
  match ← fid.getDecl with
  | .ldecl (value := v) .. => unfoldLetHead v
  | _ => return e

/-- Subscript digits, for naming the definitions `κ₁`, `κ₂`, … -/
def subscript (i : Nat) : String :=
  (toString i).map fun c => Char.ofNat (0x2080 + (c.toNat - '0'.toNat))

/-- Substitute the terms of `subst` throughout `e`. -/
def substTerms (subst : Array (Expr × Expr)) (e : Expr) : Expr :=
  if subst.isEmpty then e
  else e.replace fun s => (subst.find? fun p ↦ p.1 == s).map Prod.snd

/-- Apply the instance arguments a term is still waiting for. `mkAppM` leaves those that come
after the last explicit argument it was given. -/
partial def saturateInstances (e : Expr) : MetaM Expr := do
  match ← whnf (← inferType e) with
  | .forallE _ d _ bi =>
    if bi.isInstImplicit then saturateInstances (mkApp e (← synthInstance d)) else return e
  | _ => return e

/-- The last `n` arguments of an application. -/
def lastArgs (e : Expr) (n : Nat) : Array Expr :=
  let as := e.getAppArgs
  as[(as.size - n)...*]

/-- The kernels at the leaves of the `⊗ₖ` spine of a trace kernel: one per `←` of the program. -/
partial def compProdLeaves (P : Expr) : Array Expr :=
  if P.isAppOf ``ProbabilityTheory.Kernel.compProd then
    let as := lastArgs P 2
    compProdLeaves as[0]! ++ compProdLeaves as[1]!
  else #[P]

/-- Introduce `base := value` as a local definition, reusing one already in the context if it has
that same value. -/
def localDefFor (g : MVarId) (base : Name) (value : Expr) : MetaM (MVarId × Expr) :=
  g.withContext do
    let value ← instantiateMVars value
    for d in ← getLCtx do
      if let .ldecl (fvarId := fid) (value := v) .. := d then
        if (← instantiateMVars v) == value then return (g, .fvar fid)
    let name := (← getLCtx).getUnusedName base
    let g ← g.define name (← inferType value) value
    let (fid, g) ← g.intro1P
    return (g, .fvar fid)

/-- Give every kernel of the `⊗ₖ` spine of `P` that is too big to read a local definition of its
own. Returns the new goal and the substitution to apply to the statements being added. -/
def abstractKernels (g : MVarId) (P : Expr) : MetaM (MVarId × Array (Expr × Expr)) := do
  let mut g := g
  let mut subst : Array (Expr × Expr) := #[]
  let mut i := 1
  for κ in compProdLeaves (← instantiateMVars P) do
    if (← g.withContext <| tooWide κ) && !subst.any (·.1 == κ) then
      let (g', fv) ← localDefFor g (Name.mkSimple ("κ" ++ subscript i)) κ
      g := g'
      subst := subst.push (κ, fv)
      i := i + 1
  return (g, subst)

/-- `prog`, `P` and `out` of a proof of `RDo.HasTrace prog P out`. -/
def traceParts (h : Expr) : MetaM (Expr × Expr × Expr) := do
  let ty ← instantiateMVars (← inferType h)
  unless ty.isAppOfArity ``HasTrace 9 do
    throwError "rdo_trace: not a `HasTrace` statement: {ty}"
  let as := lastArgs ty 3
  return (as[0]!, as[1]!, as[2]!)

/-- Try to read `prog` as the coercion of a `Kernel`, so that the trace kernel is the user's own
kernel rather than a wrapper. -/
def asKernel? (prog : Expr) : MetaM (Option Expr) := do
  let (γ, α) ← forallBoundedTelescope (← inferType prog) (some 1) fun cs body ↦ do
    return (← inferType cs[0]!, (← whnfR body).getAppArgs[0]!)
  let κ ← mkFreshExprMVar (← saturateInstances (← mkAppM ``ProbabilityTheory.Kernel #[γ, α]))
  unless ← isDefEq (← mkAppM ``DFunLike.coe #[κ]) prog do return none
  let κ ← instantiateMVars κ
  if κ.hasExprMVar then return none
  unless (← trySynthInstance (← mkAppM ``IsMarkovKernel #[κ])) matches .some _ do return none
  return some κ

/-! ## Building the trace -/

/-- The tactic's state: the side conditions produced so far. -/
abbrev TraceM := StateRefT (Array MVarId) MetaM

/-- Record a side condition and return the proof term standing for it. -/
def sideGoal (type : Expr) : TraceM Expr := do
  let m ← mkFreshExprSyntheticOpaqueMVar type
  modify (·.push m.mvarId!)
  return m

/-- Look through the definitions heading a program until one of the constructs the tactic knows
about shows up. -/
partial def unfoldProgram (prog : Expr) (fuel : Nat) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  let some n ← programHeadDef? prog | return none
  -- Never unfold the `Kernel` coercion: a kernel is a leaf, not a definition to look through.
  if n == ``DFunLike.coe then return none
  let prog' ← deltaExpand prog (· == n)
  if prog' == prog then return none
  match ← shapeOf prog' with
  | .leaf | .const => unfoldProgram prog' (fuel - 1)
  | _ => return some prog'

/-- Look through the definitions heading a program until an `rdo` construct — not merely a known
shape — shows up. This is what tells an `rdo` program apart from a distribution such as
`gaussianReal`, whose body happens to be an `ite`. -/
partial def unfoldToRdoProgram (prog : Expr) (fuel : Nat) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  let some n ← programHeadDef? prog | return none
  if n == ``DFunLike.coe then return none
  let prog' ← deltaExpand prog (· == n)
  if prog' == prog then return none
  match ← shapeOf prog' with
  | .mBind | .mPure | .forIn .. | .breakRunK => return some prog'
  | .leaf | .const => unfoldToRdoProgram prog' (fuel - 1)
  | _ => return none

/-- Build the trace of `prog : γ → Measure β`.

`depth` counts how many trace coordinates the ambient parameter `γ` has accumulated from the binds
above; it is what licenses the `HasTrace.prodMkRight` step, which is the step that records in the
*type* of the trace kernel that a draw does not read the draws before it.

`root` marks the program the user asked about. A subprogram carrying an `IsMarkov` instance is a
leaf — that is the granularity knob — but the program at the root is the one being traced, so
there its own instance must not stop the traversal. -/
partial def traceCore (prog : Expr) (depth : Nat) (fuel : Nat) (root : Bool := false) :
    TraceM Expr := do
  let prog ← instantiateMVars prog
  if depth > 0 then
    if let some h ← tryWeaken prog depth fuel then return h
  if let some h ← tryRecord prog then return h
  let shape ← shapeOf prog
  let prf ← withTraceNode `rdo_trace (fun _ ↦ return m!"{shape}: {prog}") do
    match shape with
    | .mPure => tracePure prog
    | .mBind => traceBind prog depth fuel
    | _ => traceLeaf prog depth fuel root
  normalizeOut prf
where
  /-- Reduce the projections the combinators pile up in the readout, so that the trace stays
  readable and the continuations built from it stay small. -/
  normalizeOut (prf : Expr) : TraceM Expr := do
    let (prog, P, out) ← traceParts prf
    let out' ← betaProj out
    let P' ← betaProj P
    if out' == out && P' == P then return prf
    mkExpectedTypeHint prf (← mkAppM ``HasTrace #[prog, P', out'])
  /-- `fun q : Γ × Ω ↦ prog' q.1`: a subprogram that does not read the last draw. -/
  tryWeaken (prog : Expr) (depth fuel : Nat) : TraceM (Option Expr) := do
    let dom ← whnfR (← inferType prog).bindingDomain!
    unless dom.isAppOfArity ``Prod 2 do return none
    let Γ := dom.appFn!.appArg!
    let Ω := dom.appArg!
    let prog'? ← withLocalDeclD `c Γ fun c ↦ withLocalDeclD `w Ω fun w ↦ do
      let body ← betaProj (mkApp prog (← mkAppM ``Prod.mk #[c, w]))
      if body.containsFVar w.fvarId! then return none
      return some (← mkLambdaFVars #[c] body)
    let some prog' := prog'? | return none
    trace[rdo_trace] "weakening: the draw does not read the last coordinate"
    let h ← traceCore prog' (depth - 1) fuel
    let prf ← mkAppM ``HasTrace.prodMkRight #[Ω, h]
    let (prog'', _, _) ← traceParts prf
    unless ← isDefEq prog'' prog do return none
    return some prf
  /-- A value the program marked with `record`: a coordinate of its own, holding a deterministic
  function of everything drawn before it. -/
  tryRecord (prog : Expr) : TraceM (Option Expr) := do
    let progE ← etaExpand (← whnfR prog)
    let f? ← lambdaBoundedTelescope progE 1 fun cs body ↦ do
      let body ← whnfR body
      unless body.isAppOfArity ``RDo.record 3 do return none
      return some (← mkLambdaFVars cs (← betaProj body.appArg!))
    let some f := f? | return none
    trace[rdo_trace] "recorded value"
    let hf ← sideGoal (← mkAppM ``Measurable #[f])
    return some (← mkAppM ``HasTrace.record #[hf])
  /-- `return e`. -/
  tracePure (prog : Expr) : TraceM Expr := do
    let prog ← etaExpand (← whnfR prog)
    let g ← lambdaBoundedTelescope prog 1 fun cs body ↦ do
      let body ← whnfR body
      unless body.isAppOfArity ``MeasurableSpacePure.mPure 5 do
        throwError "rdo_trace: expected `mPure`, got {body}"
      mkLambdaFVars cs body.getAppArgs[4]!
    let hg ← sideGoal (← mkAppM ``Measurable #[g])
    mkAppM ``HasTrace.pure #[hg]
  /-- `let x ← p; q`. -/
  traceBind (prog : Expr) (depth fuel : Nat) : TraceM Expr := do
    let progE ← etaExpand (← whnfR prog)
    let (p, cont) ← lambdaBoundedTelescope progE 1 fun cs body ↦ do
      let c := cs[0]!
      let body ← whnfR body
      unless body.isAppOfArity ``MeasurableSpaceBind.mBind 8 do
        throwError "rdo_trace: expected `mBind`, got {body}"
      let as := body.getAppArgs
      let α := as[2]!
      -- Eta-reduce, so that a named subprogram is recognised as itself and its `IsMarkov`
      -- instance — the granularity knob — can stop the traversal there.
      let p := (← mkLambdaFVars #[c] as[6]!).eta
      let kAbs ← mkLambdaFVars #[c] as[7]!
      let γ ← inferType c
      let cont ← withLocalDeclD `q (← mkAppM ``Prod #[γ, α]) fun q ↦ do
        let q1 ← mkAppM ``Prod.fst #[q]
        let q2 ← mkAppM ``Prod.snd #[q]
        mkLambdaFVars #[q] (← betaProj (mkAppN kAbs #[q1, q2]))
      return (p, cont)
    -- `let x ← p; return f x` adds no coordinate: only the readout changes.
    if let some f ← pureBody? cont then
      trace[rdo_trace] "deterministic tail"
      let hP ← traceCore p depth fuel
      let hf ← sideGoal (← mkAppM ``Measurable #[f])
      return ← mkAppM ``HasTrace.bindPure #[hP, hf]
    let hP ← traceCore p depth fuel
    let (_, _, out) ← traceParts hP
    let Ω := (← whnfR (← inferType out)).bindingDomain!.appArg!
    let γ := (← whnfR (← inferType prog)).bindingDomain!
    let cont' ← withLocalDeclD `q (← mkAppM ``Prod #[γ, Ω]) fun q ↦ do
      let q1 ← mkAppM ``Prod.fst #[q]
      mkLambdaFVars #[q] (← mkAppM' cont #[← mkAppM ``Prod.mk #[q1, ← mkAppM' out #[q]]])
    let hQ ← traceCore cont' (depth + 1) fuel
    let hm ← sideGoal (← mkAppM ``IsMarkov #[cont])
    let hcont ← mkAppOptM ``IsMarkov.measurable #[none, none, none, none, cont, hm]
    mkAppM ``HasTrace.bind #[hcont, hP, hQ]
  /-- `fun q ↦ mPure (f q)`, if that is what `cont` is. -/
  pureBody? (cont : Expr) : TraceM (Option Expr) := do
    let contE ← etaExpand (← whnfR cont)
    lambdaBoundedTelescope contE 1 fun qs body ↦ do
      let body ← whnfR body
      unless body.isAppOfArity ``MeasurableSpacePure.mPure 5 do return none
      return some (← mkLambdaFVars qs body.getAppArgs[4]!)
  /-- A leaf: a distribution, or a subprogram treated as one atomic draw. -/
  traceLeaf (prog : Expr) (depth fuel : Nat) (root : Bool) : TraceM Expr := do
    -- At the root, look inside the program before considering it atomic.
    if root then
      if let some prog' ← unfoldToRdoProgram prog fuel then
        trace[rdo_trace] "unfolded the program under trace to {prog'}"
        let h ← traceCore prog' depth (fuel - 1)
        let (_, P, out) ← traceParts h
        return ← mkExpectedTypeHint h (← mkAppM ``HasTrace #[prog, P, out])
    if let some κ ← asKernel? prog then
      trace[rdo_trace] "leaf: the kernel {κ} itself"
      return ← mkAppM ``HasTrace.sample #[κ]
    -- A constant family is a `Kernel.const`, which reads better than the generic wrapper.
    if (← shapeOf prog) matches .const then
      let μ? ← lambdaBoundedTelescope (← etaExpand (← whnfR prog)) 1 fun cs body ↦ do
        let body ← betaProj body
        return if body.containsFVar cs[0]!.fvarId! then none else some body
      if let some μ := μ? then
      if (← trySynthInstance (← mkAppM ``IsProbabilityMeasure #[μ])) matches .some _ then
        let γ := (← whnfR (← inferType prog)).bindingDomain!
        trace[rdo_trace] "leaf: the constant kernel at {μ}"
        let prf ← mkAppM ``HasTrace.sample #[← mkAppM ``ProbabilityTheory.Kernel.const #[γ, μ]]
        let (prog', _, _) ← traceParts prf
        if ← isDefEq prog' prog then return prf
    -- Something already known to be Markov? Then it is one atomic draw.
    let g ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``IsMarkov #[prog])
    let leftover ← closeLeaf g.mvarId!
    if ← g.mvarId!.isAssigned then
      trace[rdo_trace] "leaf: an atomic draw"
      modify (· ++ leftover.toArray)
      return ← mkAppM ``HasTrace.leaf #[prog, g]
    -- Otherwise look through the definition heading the program and carry on. Only a genuine
    -- leaf is unfolded: `ite`, `for` and friends are constructs, not definitions to look through.
    let unfolded? ←
      if (← shapeOf prog) matches .leaf | .const then unfoldProgram prog fuel else pure none
    if let some prog' := unfolded? then
      trace[rdo_trace] "unfolded to {prog'}"
      let h ← traceCore prog' depth (fuel - 1)
      let (_, P, out) ← traceParts h
      return ← mkExpectedTypeHint h (← mkAppM ``HasTrace #[prog, P, out])
    trace[rdo_trace] "leaf: `IsMarkov` handed back to the user"
    modify (·.push g.mvarId!)
    mkAppM ``HasTrace.leaf #[prog, g]

/-- Discharge a side condition `rdo_trace` produced, leaving whatever it cannot prove. -/
def dischargeSide (g : MVarId) : TacticM (List MVarId) := do
  if ← g.isAssigned then return []
  let ty ← instantiateMVars (← g.getType)
  let tac ←
    if ty.isAppOfArity ``IsMarkov 5 then `(tactic| try is_markov)
    else `(tactic| try (fun_prop (disch := measurability)))
  Lean.Elab.Tactic.run g (evalTactic tac)

/-- `rdo_trace prog` computes the trace of the `rdo` program `prog` — a family of measures, or a
single measure — and adds `htrace : RDo.HasTrace prog P out` to the context, with the trace kernel
`P` and the readout `out` built from the shape of the program: one `Kernel.compProd` factor per
`←`.

* `rdo_trace prog with h` names the hypothesis `h`.
* `rdo_trace prog (fuel := n)` looks through up to `n` definitions heading the program.

The measurability and `IsMarkov` obligations the construction leaves behind are attacked with
`is_markov` and `fun_prop (disch := measurability)`, and whatever survives is handed back.

A program's own text ends up inside its trace kernel, so any kernel too wide to print is given a
local definition `κ₁`, `κ₂`, … of its own and the hypothesis mentions only those.

Use `rdo_peel` on the resulting hypothesis to get the laws of the individual draws.
`set_option trace.rdo_trace true` prints the tree of constructs the tactic walked through. -/
syntax (name := rdoTraceTac) "rdo_trace" ppSpace term (" (" &"fuel" " := " num ")")?
  (" with " ident)? : tactic

elab_rules : tactic
  | `(tactic| rdo_trace $prog $[(fuel := $fuel?)]? $[with $name?]?) => classical do
    let fuel := (fuel?.map (·.getNat)).getD defaultUnfoldFuel
    let name := (name?.map (·.getId)).getD `htrace
    let g ← getMainGoal
    let (prf, sides) ← g.withContext do
      let e ← Term.elabTerm prog none
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      -- A program with no parameter is a constant family over `Unit`.
      let ty ← whnfR (← inferType e)
      let prog ←
        if ty.isForall then pure e
        else withLocalDeclD `u (mkConst ``Unit) fun u ↦ mkLambdaFVars #[u] e
      let (prf, sides) ← (traceCore prog 0 fuel (root := true)).run #[]
      let (prog', P, out) ← traceParts prf
      let prf ←
        if ← isDefEq prog' prog then
          mkExpectedTypeHint prf (← mkAppM ``HasTrace #[prog, P, out])
        else pure prf
      return (← instantiateMVars prf, sides)
    let (_, P, _) ← g.withContext (traceParts prf)
    let (g, subst) ← abstractKernels g P
    let type ← g.withContext do return substTerms subst (← instantiateMVars (← inferType prf))
    let (_, g) ← (← g.assert name type prf).intro1P
    let mut remaining := []
    for s in sides do
      remaining := remaining ++ (← dischargeSide s)
    replaceMainGoal (g :: remaining)

/-! ## Peeling the trace -/

/-- The measure a kernel `K` reparametrised by `ι` is constant at, when the shapes `rdo_trace`
produces make it constant: a `Kernel.const`, or a `Kernel.prodMkRight` whose base is reached
through a constant reparametrisation. Everything here is definitional, so the caller can retype a
`HasCondDistrib` at `Kernel.const _ ν` without a rewrite. -/
partial def constValue? (K ι : Expr) : MetaM (Option Expr) := do
  let K ← unfoldLetHead (← whnfR K)
  if K.isAppOf ``ProbabilityTheory.Kernel.const then
    return some (lastArgs K 1)[0]!
  if K.isAppOf ``ProbabilityTheory.Kernel.prodMkRight then
    let R := (lastArgs K 1)[0]!
    let ιTy ← whnfR (← inferType ι)
    let ι' ← withLocalDeclD `d ιTy.bindingDomain! fun d ↦ do
      mkLambdaFVars #[d] (← betaProj (← mkAppM ``Prod.fst #[mkApp ι d]))
    return ← constValue? R ι'
  -- Not a recognised wrapper: constant only if the reparametrisation is.
  let ιE ← etaExpand (← whnfR ι)
  lambdaBoundedTelescope ιE 1 fun ds body ↦ do
    let body ← betaProj body
    if body.containsFVar ds[0]!.fvarId! then return none
    return some (← mkAppM ``DFunLike.coe #[K, body])

/-- One fact produced by `rdo_peel`, with a suggested name. -/
structure PeelFact where
  suggested : Name
  proof : Expr

/-- Peel the trace kernel `P` at the parameter `c` into the law of each draw given the ones before
it, then the law of the program's result. -/
def peelFacts (h : Expr) (c : Expr) : MetaM (Array PeelFact) := do
  let (_, P, _) ← traceParts h
  let mut facts : Array PeelFact := #[]
  let P ← whnfR (← instantiateMVars P)
  if P.isAppOf ``ProbabilityTheory.Kernel.compProd then
    let as := lastArgs P 2
    let κ := as[0]!
    let Q := as[1]!
    facts := facts.push ⟨`law, ← saturateInstances (← mkAppM ``hasLaw_fst_compProd #[κ, Q, c])⟩
    let mut t ← saturateInstances (← mkAppM ``hasCondDistrib_snd_compProd_comap #[κ, Q, c])
    repeat
      match ← observing? (mkAppM ``HasCondDistrib.comap_compProd_fst #[t]) with
      | none => break
      | some f =>
        facts := facts.push ⟨`law, f⟩
        facts := facts ++ (← indepFacts f)
        t ← mkAppM ``HasCondDistrib.comap_compProd_snd #[t]
    facts := facts.push ⟨`law, t⟩
    facts := facts ++ (← indepFacts t)
  facts := facts.push ⟨`law_out, ← mkAppM ``HasTrace.hasLaw_out #[h, c]⟩
  facts.mapM fun f ↦ do
    let prf ← instantiateMVars f.proof
    let ty ← betaProj (← instantiateMVars (← inferType prf))
    return { f with proof := ← mkExpectedTypeHint prf ty }
where
  /-- When the kernel of a conditional law does not depend on what it is conditioned on, add the
  unconditional law and the independence statement. -/
  indepFacts (t : Expr) : MetaM (Array PeelFact) := do
    let ty ← instantiateMVars (← inferType t)
    unless ty.isAppOf ``HasCondDistrib do return #[]
    let as := lastArgs ty 4
    let K ← whnfR as[2]!
    unless K.isAppOf ``ProbabilityTheory.Kernel.comap do return #[]
    let ks := lastArgs K 3
    let some ν ← constValue? ks[0]! ks[1]! | return #[]
    let δ := (← whnfR (← inferType ks[1]!)).bindingDomain!
    let const ← mkAppM ``ProbabilityTheory.Kernel.const #[δ, ν]
    let tc ← observing? do
      mkExpectedTypeHint t (← mkAppM ``HasCondDistrib #[as[0]!, as[1]!, const, as[3]!])
    let some tc := tc | return #[]
    let mut out := #[]
    if let some f ← observing? (mkAppM ``HasCondDistrib.hasLaw_of_const #[tc]) then
      out := out.push ⟨`law_indep, f⟩
    if let some f ← observing? (mkAppM ``HasCondDistrib.indepFun_of_const #[tc]) then
      out := out.push ⟨`indep, f⟩
    return out

/-- `rdo_peel h c` reads the probabilistic content off a trace `h : RDo.HasTrace prog P out`, at
the parameter `c`: the law of the first draw, the conditional law of every later draw given the
draws before it, and the law of the program's result. For a draw whose kernel does not read the
draws before it, it also adds the unconditional law of that draw and its independence from them.

* `rdo_peel h c with h₁ h₂ …` names the facts in the order they are produced.

The trace measure is shared by every statement, so it is given a local definition `P` rather than
repeated; wide kernels get definitions `κ₁`, `κ₂`, … the same way (reusing any `rdo_trace` already
introduced).

For a program with no parameter, pass `()`. -/
syntax (name := rdoPeelTac) "rdo_peel" ppSpace ident ppSpace term
  (" with " (ppSpace colGt ident)+)? : tactic

elab_rules : tactic
  | `(tactic| rdo_peel $h $c $[with $names?*]?) => classical do
    let g ← getMainGoal
    let (facts, P) ← g.withContext do
      let hE ← Term.elabTerm h none
      let (_, P, _) ← traceParts hE
      let γ := (← whnfR (← inferType P)).getAppArgs[0]!
      let cE ← Term.elabTerm c γ
      Term.synthesizeSyntheticMVarsNoPostponing
      return (← peelFacts hE (← instantiateMVars cE), ← instantiateMVars P)
    -- Name the kernels that are too big to read, then the trace measure built from them: without
    -- this every statement below repeats the whole program.
    let (g₁, subst) ← abstractKernels g P
    let types ← g₁.withContext <| facts.mapM fun f ↦ do
      return substTerms subst (← instantiateMVars (← inferType f.proof))
    -- The trace measure appears in every statement, so it always gets a name of its own.
    let (g₂, subst') ← do
      if h : 0 < types.size then
        let μ := (lastArgs types[0] 1)[0]!
        if μ.isFVar then pure (g₁, #[])
        else do
          let (g', fv) ← localDefFor g₁ `P μ
          pure (g', #[(μ, fv)])
      else pure (g₁, #[])
    let names := (names?.map (·.map (·.getId))).getD #[]
    let mut g := g₂
    let mut i := 0
    for f in facts do
      let name := if h : i < names.size then names[i] else Name.mkSimple s!"{f.suggested}{i + 1}"
      let prf ← instantiateMVars f.proof
      g := (← (← g.assert name (substTerms subst' types[i]!) prf).intro1P).2
      i := i + 1
    replaceMainGoal [g]

end RDo.Tactic

end
