# Random variables for `rdo` programs

A way to get from "this `rdo` program denotes a measure" to "these are its random variables, this
is their joint law, here is the conditional law of each draw given the ones before it, and here is
which of them are independent".

Implemented in [RandomDo/Probability/Trace.lean](../RandomDo/Probability/Trace.lean) (the theory)
and [RandomDo/Probability/Tactic.lean](../RandomDo/Probability/Tactic.lean) (the `rdo_trace` and
`rdo_peel` tactics), demonstrated in
[RandomDo/Probability/Examples.lean](../RandomDo/Probability/Examples.lean) and, on `thompson`, in
[RandomDo/Probability/Thompson.lean](../RandomDo/Probability/Thompson.lean). Everything below that
is described as *done* compiles with no `sorry`.

## The idea

A measure has no random variables. So give the program a probability space of its own: the space of
its **traces**, one coordinate per `←`.

```lean
structure HasTrace (prog : γ → Measure β) (P : Kernel γ Ω) (out : γ × Ω → β) : Prop where
  measurable_out : Measurable out
  map_eq (c : γ) : (P c).map (fun ω ↦ out (c, ω)) = prog c
```

* `γ` — the program's parameters (`hist` in `thompson`, `Unit` for a closed program).
* `Ω` — the trace space: the product of the types drawn at each `←`.
* `P` — the joint law of all the draws, as a Markov kernel in the parameters.
* `out` — a **deterministic** readout reconstructing the program's result from parameters + draws.

`map_eq` says: running the program = drawing a trace and reading the answer off it. Every random
variable of interest is now a function on `(Ω, P c)`, and the program's own result is one of them
(`HasTrace.hasLaw_out`).

The whole payoff comes from *how* `P` is built. Each `←` contributes one `Kernel.compProd` factor,
so the trace kernel is a right-nested `⊗ₖ` whose shape is literally the shape of the program:

```
rdo                                    P = κ ⊗ₖ (η ⊗ₖ θ)      on Ω = ℝ × (ℝ × ℝ)
  let x ← κ c
  let y ← η (c, x)
  let z ← θ ((c, x), y)
  return x + y + z                     out (c, ω) = ω.1 + ω.2.1 + ω.2.2
```

## Program construct → trace combinator

| `rdo` construct | elaborated head | rule | trace kernel built |
|---|---|---|---|
| `let x ← p; q` | `mBind` | `HasTrace.bind` | `P ⊗ₖ Q` |
| `let x ← p; return f x` | `mBind`/`mPure` | `HasTrace.bindPure` | `P` (no new draw) |
| `return e` | `mPure` | `HasTrace.pure` | `Kernel.const _ (dirac ())` |
| a leaf distribution | — | `HasTrace.sample` / `.of_isMarkov` | the kernel itself |
| a subprogram not reading the trace so far | — | `HasTrace.prodMkRight` | `Kernel.prodMkRight` |
| `if p c then … else …` | `ite` | `HasTrace.ite` | `Kernel.piecewise` |
| reparametrisation `κ (g c)` | `comp` | `HasTrace.comp` | `Kernel.comap` |
| `for … rdo …` | `forIn` | `.of_isMarkov` (coarse) — see below | one atomic coordinate |
| `record x` | `RDo.record` | `HasTrace.record` | `Kernel.deterministic` |

`HasTrace.bind` asks for `Measurable cont` on the continuation. That is exactly the obligation
`is_markov` already discharges, so the two tactics compose: `is_markov` first, then the trace.

`HasTrace.of_isMarkov` is the granularity knob. Any subprogram already known to be Markov can be
made a *single* trace coordinate, hiding its internal `←`s. Trace only as deep as the statement you
want to prove needs.

## Recording a value as a random variable

A value the program *computes* rather than draws — a `let mut` accumulator, an intermediate
quantity — is not a coordinate, so nothing makes it a random variable. The `record` annotation
([Record.lean](../RandomDo/Probability/Record.lean)) fixes that. Writing

```
record N, S
```

on a line of an `rdo` block gives the trace a coordinate for `N` and one for `S` from that point
on. It is sugar for `N ← RDo.record N`, and `RDo.record x` is the one-point distribution at `x`, so
the program still denotes the same measure — `RDo.record_bind` says so once and for all, and
`simp (disch := is_markov) only [record_bind_of_isMarkov]` erases every `record` from a program.
All the annotation does is put a `←` in the program text where there was none, and a `←` is what
the trace is built from.

`rdo_trace` gives such a coordinate the kernel `Kernel.deterministic f`, so `rdo_peel` reports it
as being a deterministic function of everything drawn before it — and, more to the point, every
*later* draw's kernel is now written in terms of that coordinate, which is what lets you condition
on it. (`record` is a reserved token once the module is imported, so the underlying definition has
to be written `RDo.record`.)

## Reading the statements off: the peeling rule

Given the trace, the probabilistic content is extracted by one rule applied once per `←`.
`hasLaw_id_compProd` starts it, and then:

```lean
HasLaw.compProd_fst          -- law of the next draw
HasLaw.compProd_snd          -- conditional law of everything after it, given it
Kernel.sectR_compProd        -- re-expose the tail as a ⊗ₖ, so the rule applies again
HasCondDistrib.compProd_fst  -- conditional law of the next draw given the history
HasCondDistrib.compProd_snd  -- ... and of the rest, given the history *and* that draw
```

Step *k* of the peeling hands you the conditional distribution of the *k*-th draw given the first
*k−1*, and the kernel it hands you is the one written at that `←` in the program. For the chain
above, four lines of proof give

```lean
HasLaw          (fun ω ↦ ω.1)   (κ c)                                    P₃
HasCondDistrib  (fun ω ↦ ω.2.1) (fun ω ↦ ω.1)         (Kernel.sectR η c) P₃
HasCondDistrib  (fun ω ↦ ω.2.2) (fun ω ↦ (ω.1, ω.2.1)) (θ.comap …)       P₃
```

**Independence is a special case.** When a draw does not mention the earlier ones, its factor is a
`Kernel.prodMkRight`, whose section is a constant kernel
(`Kernel.sectR_prodMkRight_eq_const`); `HasCondDistrib.indepFun_of_const` and
`.hasLaw_of_const` (both already in LML) then turn the conditional law into an unconditional law
plus an `IndepFun`. So *the syntactic fact that the second `←` does not mention `x` is what
produces the independence proof* — which is the property asked for.

`RandomDo/Probability/Examples.lean` carries both halves: two independent draws with
`IndepFun` + `HasLaw` for each, and the dependent three-step chain with its conditional laws.

## The tactics

Both steps are mechanical, and both are automated.

**`rdo_trace prog with h`** walks the program — reusing `RDo.Tactic.shapeOf`, the same classifier
`is_markov` walks — applying the combinator of the table above at each node, and adds
`h : HasTrace prog P out` to the context with `P` and `out` computed. Its side conditions
(`Measurable`, `IsMarkov`) are attacked with `fun_prop (disch := measurability)` and `is_markov`,
and whatever survives is handed back as a goal. `(fuel := n)` bounds how many definitions it looks
through; `set_option trace.rdo_trace true` prints the tree it walked.

It recognises the weakening opportunity itself: when a draw does not mention the draws before it,
the factor it emits is a `Kernel.prodMkRight`, which is what makes the independence statement
available downstream. `mBind`, `mPure`, `let x ← p; return f x` (no coordinate) and leaves are
traced structurally; `ite`, `for` and early returns are traced coarsely, as one atomic draw — the
`HasTrace.ite` rule is there to be applied by hand when finer branching is wanted.

**`rdo_peel h c`** iterates the peeling rule on such a hypothesis at the parameter `c`, adding one
`HasLaw`/`HasCondDistrib` per `←` plus `HasLaw` for the program's result, and — for every draw
whose kernel turns out not to read the draws before it — the unconditional law of that draw and its
`IndepFun` from them. `with h₁ h₂ …` names the facts in order.

**Readability.** A program's own text ends up inside its trace kernel, and every statement a peeled
trace adds mentions the trace measure built from those kernels — printed in full, once per
hypothesis, that is unreadable. So anything too wide to print gets a local definition of its own:
`κ₁`, `κ₂`, … for the kernels (`rdo_trace`), `P` for the trace measure (`rdo_peel`, which reuses
the definitions `rdo_trace` already made). Each statement is then one line:

```lean
κ₁ : Kernel (Vector (Fin K × ℝ) n) ((Fin K → ℝ) × (Fin K → ℝ)) := markovKernel …
κ₂ : Kernel … := markovKernel …
h  : HasTrace (thompsonRecord hK) (κ₁ ⊗ₖ (Kernel.deterministic … ⊗ₖ (κ₂ ⊗ₖ κ₃))) fun p ↦ argmax p.2.2.2.2
P  : Measure … := (κ₁ ⊗ₖ …) hist
law1 : HasLaw Prod.fst (κ₁ hist) P
law2 : HasCondDistrib (fun ω ↦ ω.2.1) Prod.fst (… .comap (fun ω ↦ (hist, ω)) ⋯) P
…
```

The cut-off is printed width rather than subterm count, since a kernel's implicit type arguments
are large but never shown; small kernels such as `Kernel.const`, `Kernel.prodMkRight` and
`Kernel.deterministic` stay inline, which also keeps the independence detection above able to see
their shape.

Together, on the two examples above:

```lean
example : True := by
  rdo_trace (sum2 μ) with h
  rdo_peel h () with hX hY hY' hindep hout
  -- hX     : HasLaw Prod.fst μ P            hY' : HasLaw Prod.snd μ P
  -- hY     : HasCondDistrib Prod.snd Prod.fst … P
  -- hindep : Prod.fst ⟂ᵢ[P] Prod.snd
  -- hout   : HasLaw (fun ω ↦ ω.1 + ω.2) (sum2 μ) P
  trivial
```

The `Automation` section of `Examples.lean` pins those statements with `have _ : … := hX`, so the
tests fail if the tactics ever produce something else.

## Worked example: Thompson sampling

[RandomDo/Probability/Thompson.lean](../RandomDo/Probability/Thompson.lean) runs the whole thing on
`thompson`. That program is two loops — fold the history into per-arm pull counts `N` and reward
sums `S`, then draw one Gaussian posterior sample per arm into a vector `θ` — followed by
`return argmax θ`.

Naming the two stages as `rdo` programs of their own, `stats` and `sample`, the decomposition is an
equation both sides of which elaborate to the same two loops; only the `return` at the end of each
stage separates them, so it falls to `simp only [Prod.mk.eta, mBind_mPure]`:

```lean
thompson hK hist = stats hist >>=ₘ fun NS ↦ sample NS >>=ₘ fun θ ↦ mPure (argmax θ)
```

Giving `stats` and `sample` their own `IsMarkov` instances then makes `rdo_trace` stop at each —
the granularity knob — so the trace it finds is the readable two-coordinate one,
`statsK ⊗ₖ sampleK.comap Prod.snd`, rather than the two raw loop terms. (Without those instances
`rdo_trace` still succeeds, and still splits the program in two; it just carries the unfolded loops
in the kernels.) `rdo_peel` then delivers, on the trace measure:

```lean
HasLaw         (fun ω ↦ ω.1) (stats hist)                     -- the statistics
HasCondDistrib (fun ω ↦ ω.2) (fun ω ↦ ω.1) sampleK            -- θ given them, and nothing else
HasLaw         (fun ω ↦ argmax ω.2) (thompson hK hist)        -- the action played
```

The middle line is the substantive one: it says `θ` depends on the history *only through*
`(N, S)`, which is the whole content of "Thompson sampling is a function of the sufficient
statistics" — and it is read off the program text, not proved by hand.

The `Record` section of the same file shows the annotation at work on the monolithic program:
`record N, S` just before the sampling loop turns `N` and `S` into coordinates two and three of a
four-coordinate trace, without restructuring the program into stages, and `thompsonRecord_eq` shows
the annotated program is the same measure as `thompson`. The sampling loop's kernel is then written
in terms of those coordinates, so `θ` can be conditioned on `N` and `S` individually.

What is missing there is inside the sampling loop: `θ`'s `K` coordinates are drawn independently,
and that is exactly the statement the coarse loop trace cannot make. See below.

## What is left

### 1. Loops at per-iteration granularity

Today a `for` loop is traced coarsely: it is Markov, so `HasTrace.of_isMarkov` makes the whole loop
one coordinate holding its final accumulator. That already gives the conditional law of *the loop's
result* given everything before it — often enough — but not the law of the individual iterations.
The `Loop` section of `Examples.lean` does exactly this: a loop summing `l.length` draws, followed
by a draw distributed as `η S` given the loop's result `S`.

For per-iteration granularity the obstacle is that the number of `⊗ₖ` factors is symbolic, so the
trace type cannot be a fixed nest of products. Two shapes work:

* **`List α`**, the values drawn in order. Fits this repo well: `RandomDo/Measurable.lean` already
  provides the σ-algebra on `List α` and `measurable_cons`. The definitions are

  ```lean
  noncomputable def loopTrace (K : ι → σ → Measure α) (upd : ι → σ → α → σ) :
      List ι → σ → Measure (List α)
    | [], _ => Measure.dirac []
    | i :: l, s => (K i s).bind fun z ↦ (loopTrace K upd l (upd i s z)).map (z :: ·)

  def loopOut (upd : ι → σ → α → σ) : List ι → σ → List α → σ
    | [], s, _ => s
    | _ :: _, s, [] => s
    | i :: l, s, z :: zs => loopOut upd l (upd i s z) zs
  ```

  and the two theorems needed are `IsMarkov (loopTrace K upd l)` and
  `forIn l s (fun i s ↦ (K i s).map fun z ↦ .yield (upd i s z)) = (loopTrace K upd l s).map
  (loopOut upd l s)`, both by induction on `l`. The unrolling equations for the induction already
  exist as `forIn_nil` / `forIn_cons` in [Lemmas.lean](../RandomDo/Tactic/Lemmas.lean) — they are
  `private` and would need exposing. A third theorem, peeling the head off `loopTrace`, then gives
  the conditional law of iteration `k` given iterations `< k`.

* **`Π i : Iic n, α`** via Mathlib's `Kernel.partialTraj`. More machinery, but it is the *same*
  history type as `Learning.Algorithm.policy`, so a loop traced this way plugs straight into LML's
  `IsAlgEnvSeq` filtration and conditional-distribution API.

Either shape would then get its own `traceCore` case in
[Tactic.lean](../RandomDo/Probability/Tactic.lean), next to `mBind`.

Loop bodies with `break` / early `return` change the number of draws per iteration and need the
`Break.runK` construct handled too; a `Sum`-shaped trace space is the natural target, exactly as for
`ite` branches drawing in different spaces. The same `Sum` construction is what `rdo_trace` would
need to trace an `ite` finely rather than as one atomic draw.

## The algorithm's draws inside an `IsAlgEnvSeq`

[RandomDo/Probability/AlgTrace.lean](../RandomDo/Probability/AlgTrace.lean) closes the loop with
LML. `IsAlgEnvSeq A Y alg env P` says nothing about *how* the algorithm produced its actions: when
`alg` comes from an `rdo` program, the draws that program makes are not random variables of
`(Ω, P)` at all. This file makes them available.

A `RDo.AlgTrace alg Ω` bundles what `rdo_trace` produces for a policy: one space `Ω` of internal
draws, a kernel `K n` for their law at step `n` given the history, and a readout `out n`
reconstructing the action. From it, `AlgTrace.algorithm` is an algorithm whose actions are pairs
`(draws, action)` — the draws first, then the action *deterministically* read off them, which is
what makes the two halves fall straight out of the peeling rule:

* `AlgTrace.isAlgEnvSeq_snd` — forgetting the draws turns an algorithm-environment sequence for the
  traced algorithm into one for `alg`;
* `AlgTrace.hasCondDistrib_trace` — the draws have conditional law `K n` given the history;
* `AlgTrace.action_ae_eq` — and the action is `out n` of the history and the draws.

Since the traced algorithm faces the same environment, LML's `isAlgEnvSeq_unique` gives the
punchline, `AlgTrace.exists_isAlgEnvSeq_trace`: **any** algorithm-environment sequence may be
replaced by one on a space that also carries the draws, with the same trajectory law. The space is
existentially quantified precisely because it does not matter — no extension theorem is needed,
since the traced sequence is built on LML's canonical Ionescu–Tulcea space and uniqueness transfers
every conclusion about the actions and feedbacks back.

### The `alg_env_trace` tactic

`alg_env_trace tr` does the replacement in one step. Given an `IsAlgEnvSeq` hypothesis in the
context and an `AlgTrace tr` for its algorithm, it abstracts the goal — and every hypothesis
mentioning the probability space, the measure or the two sequences, so nothing is silently lost —
away from that space, and leaves two goals:

* **`traced`**: the same statement on a space that also carries the draws `T`, with `hT₀` its law,
  `hT` its conditional law given the history, and `hA₀`/`hA` the equations expressing each action
  as the readout of the history and the draws;
* **`transfer`**: the obligation that the statement depends only on the law of the trajectory, with
  both sequences' `IsAlgEnvSeq` available (so measurability is at hand).

That second goal is what makes the move sound rather than a hole: the traced sequence lives on a
different space, and all that relates it to the original is `isAlgEnvSeq_unique`.

```lean
example … (h : IsAlgEnvSeq A Y (alg hK) env P) : P.map (A 0) = Measure.dirac ⟨0, hK⟩ := by
  alg_env_trace (trace hK) with Ω P A Y Z hseq hZ₀ hZ hA₀ hA
  case traced => exact hseq.hasLaw_action_zero.map_eq
  case transfer => …
```

after which the context reads

```
Ω : Type          P : Measure Ω        A : ℕ → Ω → Fin K    Y Z : ℕ → Ω → ℝ
hseq : IsAlgEnvSeq A Y (alg hK) env P
hZ₀  : HasLaw (Z 0) (trace hK).K0 P
hZ   : ∀ n, HasCondDistrib (Z (n+1)) (history A Y n) ((trace hK).K n) P
hA   : ∀ n, A (n+1) =ᵐ[P] fun ω ↦ (trace hK).out n (history A Y n ω, Z (n+1) ω)
```

`alg_env_trace tr using h` names the hypothesis rather than searching for one; `with` names the
introduced variables. The space, its σ-algebra, the measure, the `IsProbabilityMeasure` hypothesis
and the two sequences all have to be local hypotheses, since the goal is abstracted over them.
`AlgTrace.wlog_trace` is the principle behind it, usable directly.

`RDo.Example` at the end of the file runs the whole thing end to end on a toy policy written as an
`rdo` program: `rdo_trace` gives the trace, the `AlgTrace` packages it, `Example.exists_noise`
hands back the noise the policy draws at each step, and the last example drives the tactic.

To do the same for `thompson` one still needs the measurable equivalence between `Iic n → 𝓐 × 𝓨`
and `Vector (𝓐 × 𝓨) (n + 1)` that turns it into a policy — `Vector.v_equiv` in
`RandomDo/Tactic/Examples.lean`, which is a `sorry` there (and stated one element short of the
right cardinality). Everything downstream of that point is done.
