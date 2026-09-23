import RandomDo.Monad.Instances
import RandomDo.Measurable
import RandomDo.Tactic.IsMarkov.Elab
import RandomDo.Tactic.Computable.Polymorphic
import RandomDo.ForMathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Prototype: the graded trace monad, with a proving and a running instance

A program is written once over a `GradedMonad m`, drawing through `HasGaussianG`. Every
`let x ← …` records `x` under its own name: the grade `l` of `m l α` lists the recorded variables
with their names and is inferred from the program. Two instances:

* `TraceM l α := Measure (Rec l × α)`, the joint law of the recorded variables and the result,
  on the nested product `Rec l`. That product is internal: `gen_projections p` moves to the
  `Fin`-indexed space Mathlib's probability library speaks, defining `p.Ω := Fin n → T`,
  `p.toFin : Rec l → p.Ω`, `p.P : Measure p.Ω`, and `p.x : p.Ω → T` for each recorded `x`
  (`fun ω ↦ ω i`). The laws are computed by `simp` with the monad laws at `Measure`.
* `SamplerM l α := RandPCG IO α`, which ignores the grade and samples.

Not part of any library: open it in the editor, it elaborates with the project's imports.
-/

open Lean Meta Elab Term Command Do MeasureTheory ProbabilityTheory NumLean
open MeasurableSpaceBind MeasurableSpacePure LawfulMeasurableSpaceMonad

/-! ## Grades and trace spaces -/

/-- A type with a measurable structure, as a grade entry. -/
structure MType where
  carrier : Type
  [inst : MeasurableSpace carrier]

attribute [instance] MType.inst

/-- Print a grade entry as its carrier. -/
@[app_unexpander MType.mk] def unexpandMType : PrettyPrinter.Unexpander
  | `($_ $T $_) => `($T)
  | `($_ $T) => `($T)
  | _ => throw ()

/-- A grade: the recorded variables, in order. -/
abbrev Grade := List (String × MType)

/-- The trace space of a grade: one factor per recorded variable. -/
@[reducible] def Rec : Grade → Type
  | [] => PUnit
  | (_, T) :: l => T.carrier × Rec l

instance Rec.instMeasurableSpace : (l : Grade) → MeasurableSpace (Rec l)
  | [] => inferInstance
  | _ :: l => letI := Rec.instMeasurableSpace l; inferInstance

def Rec.append : {l₁ l₂ : Grade} → Rec l₁ → Rec l₂ → Rec (l₁ ++ l₂)
  | [], _, _, r₂ => r₂
  | _ :: _, _, (a, r₁), r₂ => (a, Rec.append r₁ r₂)

lemma Rec.measurable_append_uncurry : ∀ {l₁ l₂ : Grade},
    Measurable fun p : Rec l₁ × Rec l₂ ↦ Rec.append p.1 p.2
  | [], _ => measurable_snd
  | _ :: l₁, l₂ => by
    change Measurable fun p : (_ × Rec l₁) × Rec l₂ ↦ (p.1.1, Rec.append p.1.2 p.2)
    exact measurable_fst.fst.prodMk
      (Rec.measurable_append_uncurry.comp (measurable_fst.snd.prodMk measurable_snd))

@[fun_prop]
lemma Rec.measurable_append {l₁ l₂ : Grade} {X : Type*} [MeasurableSpace X]
    {f : X → Rec l₁} {g : X → Rec l₂} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x ↦ Rec.append (f x) (g x) :=
  Rec.measurable_append_uncurry.comp (hf.prodMk hg)

/-! ## The graded monad, and the classes a program draws through -/

/-- A monad graded by the recorded variables. -/
class GradedMonad (m : Grade → (α : Type) → [MeasurableSpace α] → Type) where
  gPure {α : Type} [MeasurableSpace α] : α → m [] α
  gBind {l₁ l₂ : Grade} {α β : Type} [MeasurableSpace α] [MeasurableSpace β] :
    m l₁ α → (α → m l₂ β) → m (l₁ ++ l₂) β
  /-- Record `a` under the name `n`: one more coordinate of the trace. Inserted by the
  elaborator after every `let x ← …`. -/
  grecord (n : String) {α : Type} [MeasurableSpace α] (a : α) : m [(n, MType.mk α)] Unit

export GradedMonad (gPure gBind grecord)

/-- A graded monad that can draw from a Gaussian with values in `R`. -/
class HasGaussianG (m : Grade → (α : Type) → [MeasurableSpace α] → Type) (R : Type)
    [MeasurableSpace R] where
  gaussian : R → R → m [] R

/-! ### The proving instance: the joint law -/

/-- The trace monad: the joint law of the recorded variables and the result. -/
def TraceM (l : Grade) (α : Type) [MeasurableSpace α] : Type := Measure (Rec l × α)

/- The operations are `rdo`-shaped programs at `Measure`, so that `is_markov` reads them. -/

noncomputable instance TraceM.gradedMonad : GradedMonad TraceM where
  gPure a := (mPure ((), a) : Measure (Rec [] × _))
  gBind {l₁ l₂ _ _ _ _} x f :=
    ((x : Measure (Rec l₁ × _)) >>=ₘ fun p ↦
      (f p.2 : Measure (Rec l₂ × _)) >>=ₘ fun q ↦ mPure (Rec.append p.1 q.1, q.2)
      : Measure (Rec (l₁ ++ l₂) × _))
  grecord n α _ a := (mPure ((a, ()), ()) : Measure (Rec [(n, MType.mk α)] × Unit))

noncomputable instance TraceM.hasGaussian : HasGaussianG TraceM ℝ where
  gaussian μ v := (gaussianReal μ (Real.toNNReal v) >>=ₘ fun x ↦ mPure ((), x) : Measure (Rec [] × ℝ))

/-! ### The running instance: a sampler that ignores the grade -/

/-- The sampling monad, graded trivially. -/
def SamplerM (_l : Grade) (α : Type) [MeasurableSpace α] : Type := RandPCG IO α

instance SamplerM.gradedMonad : GradedMonad SamplerM where
  gPure a := (pure a : RandPCG IO _)
  gBind x f := (bind (x : RandPCG IO _) f : RandPCG IO _)
  grecord _ _ _ _ := (pure () : RandPCG IO Unit)

instance SamplerM.hasGaussian : HasGaussianG SamplerM Float where
  gaussian μ v := (normal' μ v : RandPCG IO Float)

/-! ## The `DoOps`: `gPure`/`gBind` of whatever `m` the expected type names -/

def gradeElem : Expr := mkApp2 (mkConst ``Prod [.zero, .one]) (mkConst ``String) (mkConst ``MType)

def mkGM (m l α σ : Expr) : Expr := mkApp3 m l α σ

def gradedOps : DoOps := { DoOps.default with
  mkPureApp α e := do
    let m := (← read).monadInfo.m
    let e ← Term.ensureHasType α e
    let σ ← instantiateMVars (← mkInstMVar (mkApp (mkConst ``MeasurableSpace [0]) α))
    let inst ← instantiateMVars (← mkInstMVar (mkApp (mkConst ``GradedMonad) m))
    return mkAppN (mkConst ``GradedMonad.gPure) #[m, inst, α, σ, e]
  mkBindApp α β e k := do
    let m := (← read).monadInfo.m
    Term.synthesizeSyntheticMVarsNoPostponing
    let σα ← mkInstMVar (mkApp (mkConst ``MeasurableSpace [0]) α)
    let σβ ← mkInstMVar (mkApp (mkConst ``MeasurableSpace [0]) β)
    let eType ← instantiateMVars (← inferType e)
    let .app (.app (.app _ l₁) _) _ := eType.consumeMData | throwError "graded bind: {e} : {eType}"
    let kType ← instantiateMVars (← inferType k)
    let .forallE _ _ body _ := kType.consumeMData | throwError "graded bind: {k} : {kType}"
    let .app (.app (.app _ l₂) _) _ := body.consumeMData | throwError "graded bind: {k} : {kType}"
    if body.hasLooseBVars then throwError "graded bind: the grade {l₂} depends on the bound value"
    let e ← Term.ensureHasType (mkGM m l₁ α σα) e
    let k ← Term.ensureHasType (← mkArrow α (mkGM m l₂ β σβ)) k
    let σα ← instantiateMVars σα
    let σβ ← instantiateMVars σβ
    let inst ← instantiateMVars (← mkInstMVar (mkApp (mkConst ``GradedMonad) m))
    let l ← reduce (mkApp3 (mkConst ``List.append [.one]) gradeElem l₁ l₂) (skipTypes := false)
    mkExpectedTypeHint (mkAppN (mkConst ``GradedMonad.gBind) #[m, inst, l₁, l₂, α, β, σα, σβ, e, k])
      (mkGM m l β σβ)
  isPureApp? e := if e.isAppOfArity ``GradedMonad.gPure 5 then some (e.getArg! 4) else none
  splitMonadApp? type := do
    let .app mα _ := type.consumeMData | return none
    let .app ml resultType := mα.consumeMData | return none
    let .app m _ := ml.consumeMData | return none
    unless ← isType resultType do return none
    return some ({ m := m, u := 0, v := 0 }, resultType)
  mkMonadApp α := do
    let m := (← read).monadInfo.m
    let l ← mkFreshExprMVar (mkConst ``Grade)
    let σ ← mkInstMVar (mkApp (mkConst ``MeasurableSpace [0]) α)
    return mkGM m l α σ }

/-! ### Recording: every `let x ← …` records `x`

The binder name is known where the bind is built, so recording is one more step in `mkBindApp`:
`let x ← e; k` becomes `gBind e (fun x ↦ gBind (grecord "x" x) (fun _ ↦ k x))`, for every binder
the user wrote. The elaborator's own binders (`__do_lift`, `__r`, `_`) are not recorded. -/

def recordingOps : DoOps := { gradedOps with
  mkBindApp α β e k := do
    let k ← instantiateMVars k
    let .lam x _ _ _ := k | gradedOps.mkBindApp α β e k
    if x.hasMacroScopes || x.isInternal || x == `_ then return ← gradedOps.mkBindApp α β e k
    let σα ← instantiateMVars (← mkInstMVar (mkApp (mkConst ``MeasurableSpace [0]) α))
    let k' ← withLocalDeclD x α fun xv ↦ do
      let recd := mkAppN (mkConst ``GradedMonad.grecord)
        #[(← read).monadInfo.m, ← mkInstMVar (mkApp (mkConst ``GradedMonad) (← read).monadInfo.m),
          mkStrLit x.toString, α, σα, xv]
      let rest ← withLocalDeclD `__r (mkConst ``Unit) fun u ↦ mkLambdaFVars #[u] (k.beta #[xv])
      let inner ← gradedOps.mkBindApp (mkConst ``Unit) β recd rest
      mkLambdaFVars #[xv] inner
    gradedOps.mkBindApp α β e k' }

syntax (name := gdoKind) "gdo" doSeq : term
@[term_elab gdoKind] def elabGdo : TermElab := fun stx et? => do
  let `(gdo $doSeq) := stx | throwUnsupportedSyntax
  elabDoWith recordingOps doSeq et?

/-- `rdef p : m α := …` defines the program `p`, of type `m l α` for the grade `l` inferred from
the body. A `def` cannot infer a hole in its header from its body, so this expands to a `def`
with the ascription `(gdo … : m _ α)` in the body. -/
macro "rdef " n:ident " : " m:ident α:term:max " := " body:doSeq : command =>
  `(def $n := (gdo $body : $m _ $α))

/-! ## Vectors: from the nested product to `Fin n → T` -/

@[fun_prop]
lemma Measurable.vecCons {X α : Type*} [MeasurableSpace X] [MeasurableSpace α] {n : ℕ}
    {f : X → α} {g : X → Fin n → α} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x ↦ Matrix.vecCons (f x) (g x) :=
  measurable_finCons.comp (hf.prodMk hg)

@[fun_prop]
lemma measurable_vecEmpty {X α : Type*} [MeasurableSpace X] [MeasurableSpace α] :
    Measurable fun _ : X ↦ (Matrix.vecEmpty : Fin 0 → α) :=
  measurable_const

/-! ## Generating the named projections and the trace measure -/

partial def readGrade (l : Expr) : MetaM (List (String × Expr)) := do
  match_expr l with
  | List.nil _ => return []
  | List.cons _ hd tl =>
    let_expr Prod.mk _ _ n T := hd | throwError "not a grade entry: {hd}"
    let .lit (.strVal s) := n | throwError "not a name literal: {n}"
    let_expr MType.mk T _ := T | throwError "not a measurable type: {T}"
    return (s, T) :: (← readGrade tl)
  | _ => throwError "not a literal grade: {l}"

/-- `gen_projections p`, for a program whose recorded variables all have the same type `T`,
defines the `Fin`-indexed trace space and everything on it:

* `p.Ω := Fin n → T`, and `p.toFin : Rec l → p.Ω` with `p.measurable_toFin`;
* `p.P : Measure p.Ω`, the joint law of the recorded variables;
* `p.x : p.Ω → T`, `fun ω ↦ ω i`, with `p.measurable_x`, for each recorded `x` at position `i`. -/
elab "gen_projections " n:ident : command => liftTermElabM do
  let c ← realizeGlobalConstNoOverload n
  let ty ← instantiateMVars (← getConstInfo c).type
  let .app (.app (.app _ l) _) _ := ty | throwError "{c} is not a graded program: {ty}"
  let l ← reduce l (skipTypes := false)
  let ΩRec := mkApp (mkConst ``Rec) l
  let entries ← readGrade l
  let some (_, T) := entries.head? | throwError "{c} records nothing"
  for (_, T') in entries do
    unless ← isDefEq T T' do throwError "heterogeneous grade {l}: not supported by this prototype"
  let k := entries.length
  let finK := mkApp (mkConst ``Fin) (mkNatLit k)
  let Ω ← mkArrow finK T
  let define (name : Name) (type value : Expr) (compile := true) : TermElabM Unit := do
    let decl := .defnDecl <| mkDefinitionValEx (c ++ name) [] type value .abbrev .safe []
    -- `P` is a measure, hence noncomputable: add it without compiling it.
    if compile then addAndCompile decl else addDecl decl
    enableRealizationsForConst (c ++ name)
    logInfo m!"{c ++ name} : {type}"
  let prove (name : Name) (type : Expr) (tac : TSyntax ``Lean.Parser.Tactic.tacticSeq) :
      TermElabM Unit := do
    let prf ← Term.elabTermAndSynthesize (← `(by $tac)) type
    addDecl <| .thmDecl <| mkTheoremValEx (c ++ name) [] type (← instantiateMVars prf) []
  define `Ω (mkSort .one) Ω
  -- `toFin ω = ![ω.1, ω.2.1, …]`
  let toFin ← withLocalDeclD `ω ΩRec fun ω ↦ do
    let mut coords := #[]
    for i in [0:k] do
      let mut e := ω
      for _ in [0:i] do e ← mkAppM ``Prod.snd #[e]
      coords := coords.push (← mkAppM ``Prod.fst #[e])
    let mut v ← mkAppOptM ``Matrix.vecEmpty #[T]
    for e in coords.reverse do v ← mkAppM ``Matrix.vecCons #[e, v]
    mkLambdaFVars #[ω] v
  define `toFin (← mkArrow ΩRec Ω) toFin
  prove `measurable_toFin (← mkAppM ``Measurable #[mkConst (c ++ `toFin)])
    (← `(tacticSeq| unfold $(mkIdent (c ++ `toFin)):ident; fun_prop))
  let P ← Term.elabTermAndSynthesize (← `(MeasureTheory.Measure.map $(mkIdent (c ++ `toFin))
    (MeasureTheory.Measure.map Prod.fst ($(mkIdent c) : MeasureTheory.Measure _)))) none
  define `P (← inferType P) (← instantiateMVars P) (compile := false)
  for (name, _) in entries, i in [0:k] do
    let idx ← Term.elabTermAndSynthesize
      (← `(($(Syntax.mkNumLit (toString i)) : Fin $(Syntax.mkNumLit (toString k))))) finK
    let proj ← withLocalDeclD `ω Ω fun ω ↦ mkLambdaFVars #[ω] (mkApp ω idx)
    define name.toName (← mkArrow Ω T) proj
    prove (Name.mkSimple ("measurable_" ++ name)) (← mkAppM ``Measurable #[mkConst (c ++ name.toName)])
      (← `(tacticSeq| unfold $(mkIdent (c ++ name.toName)):ident; fun_prop))

/-! ## The program, written once -/

section
variable {m : Grade → (α : Type) → [MeasurableSpace α] → Type} [GradedMonad m]
  {R : Type} [MeasurableSpace R] [Add R] [OfNat R 0] [OfNat R 1] [HasGaussianG m R]

-- Draw `x ∼ 𝒩(0, 1)`, then `y ∼ 𝒩(x, 1)`, and return their sum. Both draws are recorded.
rdef sum2 : m R :=
  let x ← HasGaussianG.gaussian (m := m) (0 : R) 1
  let y ← HasGaussianG.gaussian (m := m) x 1
  return x + y

end

#check @sum2

/-! ## Running it -/

#eval IO.runRandPCGWith 42 (sum2 (m := SamplerM) (R := Float) : RandPCG IO Float)

/-! ## Proving about it -/

/-- The program read as a joint law. -/
noncomputable def sum2T := sum2 (m := TraceM) (R := ℝ)

#check sum2T

gen_projections sum2T

/-- `Measure.bind` and `Measure.dirac` are the monad's `mBind` and `mPure`, syntactically. -/
lemma Measure.bind_eq_mBind {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (f : α → Measure β) : μ.bind f = μ >>=ₘ f := rfl

lemma Measure.dirac_eq_mPure {α : Type} [MeasurableSpace α] (a : α) :
    Measure.dirac a = (mPure a : Measure α) := rfl

/-- A draw that is not used afterwards integrates out. -/
lemma mBind_const {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    [IsProbabilityMeasure μ] (ν : Measure β) : (μ >>=ₘ fun _ ↦ ν) = ν := by
  change μ.bind _ = ν
  rw [Measure.bind_const, measure_univ, one_smul]

/-- The side conditions of the monad laws at `Measure`: measurability of a continuation, which is
the Markov property of the program it is. -/
macro "markov_side" : tactic =>
  `(tactic| first
    | fun_prop
    | (apply (config := { allowSynthFailures := true }) IsMarkov.measurable; is_markov))

/-- Unfold the program at `TraceM` down to `>>=ₘ`/`mPure`, and normalise with the monad laws. -/
macro "trace_normalize" : tactic =>
  `(tactic| (
    -- `delta`, not `simp`: the unfolded grades are `[] ++ l`, equal to `l` only by unfolding
    -- `List.append`, which `simp`'s congruence closure does not do.
    delta sum2T sum2 TraceM.gradedMonad TraceM.hasGaussian
    dsimp only [id]
    simp only [Real.toNNReal_one]
    simp (disch := fun_prop) only [← Measure.bind_dirac_eq_map]
    simp only [Measure.bind_eq_mBind, Measure.dirac_eq_mPure]
    simp (disch := markov_side) only [mBind_assoc, mPure_mBind, Rec.append]))

/-- The internal joint law, on the nested product, in composition-product form. -/
instance : IsMarkov fun x : ℝ ↦ gaussianReal x 1 := by is_markov

/-- The kernel `x ↦ 𝒩(x, 1)`. -/
noncomputable def gk : Kernel ℝ ℝ := IsMarkov.toKernel fun x : ℝ ↦ gaussianReal x 1

instance : IsMarkovKernel gk := by unfold gk; infer_instance

@[simp] lemma gk_apply (x : ℝ) : gk x = gaussianReal x 1 := rfl

lemma sum2T.rec_eq :
    (sum2T : Measure _).map Prod.fst = (gaussianReal 0 1 ⊗ₘ gk).map fun p ↦ (p.1, (p.2, ())) := by
  rw [Measure.map_compProd_eq_bind _ _ (by fun_prop)]
  simp only [gk_apply]
  trace_normalize

/-- **The joint law of `(x, y)`**, on `Fin 2 → ℝ`: `x ∼ 𝒩(0, 1)`, then `y ∼ 𝒩(x, 1)`. -/
theorem sum2T.P_eq : sum2T.P = (gaussianReal 0 1 ⊗ₘ gk).map fun p ↦ ![p.1, p.2] := by
  delta sum2T.P
  rw [sum2T.rec_eq, Measure.map_map sum2T.measurable_toFin (by fun_prop)]
  rfl

/-- The marginal law of `x`. -/
theorem sum2T.map_x : sum2T.P.map sum2T.x = gaussianReal 0 1 := by
  rw [sum2T.P_eq, Measure.map_map sum2T.measurable_x (by fun_prop)]
  simp only [Function.comp_def, sum2T.x, Matrix.cons_val_zero]
  rw [Measure.map_compProd_eq_bind _ _ (by fun_prop)]
  simp only [gk_apply]
  simp (disch := fun_prop) only [← Measure.bind_dirac_eq_map]
  simp only [Measure.bind_eq_mBind, Measure.dirac_eq_mPure]
  simp only [mBind_const, mBind_mPure]

/-- `x` has law `𝒩(0, 1)` on the trace space. -/
theorem sum2T.hasLaw_x : HasLaw sum2T.x (gaussianReal 0 1) sum2T.P :=
  ⟨sum2T.measurable_x.aemeasurable, sum2T.map_x⟩

#check sum2T.P
#check sum2T.hasLaw_x
#check sum2T.P_eq
