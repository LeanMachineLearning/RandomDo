# A reading guide to `Test/RandomSource.lean`

This guide walks through [`Test/RandomSource.lean`](../Test/RandomSource.lean) from top to
bottom. It assumes you know what an `rdo` block is and roughly what a `MeasurableSpaceMonad` is: a
monad whose types carry measurable spaces, with `mPure`/`mBind` (`>>=ₘ`) and, at `m := Measure`,
`mPure = dirac` and `mBind = Measure.bind`. Everything else is introduced before it is used.

Each section introduces one idea in three steps: **the picture** (what to imagine), **the Lean**
(the declarations, with links), and **why it is there** (what later sections use it for). Proof
sketches are marked *(proof, skippable)*: they explain how a result is obtained, and nothing later
depends on reading them.

Line numbers in the links are those of the file as it is now. They will drift as the file changes;
the declaration names will not.

---

## 0. The problem this file solves

An `rdo` program at `m := Measure` is a *measure*. For example,

```lean
rdo
  let x ← gaussianReal 0 1
  let y ← gaussianReal 0 1
  return x + y
```

is the law of `x + y`. That is all it is: a measure on `ℝ`. There is no `x` and no `y` anywhere
that one could condition on or state independence of. The variables only exist inside the program
text.

For bandits this is a real obstacle. LeanMachineLearning's `IsAlgEnvSeq O A Y alg env P` asks for
observations `O n`, actions `A n` and feedbacks `Y n` as *functions on a probability space*
`(Ω, P)`, with prescribed conditional laws. And the statements one wants to prove about a
randomized algorithm are often about its *internal* randomness. "ε-greedy explores each arm with
probability ≥ ε/K" is about the exploration coin, which is not an observation, an action or a
feedback, and so is not a random variable anywhere.

The existing answer in the repository (`RandomDo/Probability/Trace.lean`, `rdo_trace`,
`rdo_peel`) builds, *for each program*, a space of draws shaped like the program: one
`Kernel.compProd` factor per `←`. That works for straight-line programs, but the shape of the
space has to follow the shape of the program, which does not fit branches (the draws differ from
branch to branch) or loops (the number of draws varies).

This file takes the opposite approach:

> **One probability space for every program**, and each program becomes a *deterministic function*
> of a point of that space.

Every value a program computes, every intermediate draw included, is then a random variable on that
one space, and branches and loops cost nothing extra.

---

## 1. The table

### The picture

Picture an infinite tree. Every node has children `0, 1, 2, …`, and each node is named by the
path from the root: `[]` is the root, `[1]` its child `1`, `[1, 0]` the child `0` of that, and so
on. Every node holds a number in `[0, 1]`, chosen uniformly at random, independently of all the
others.

A particular filling of the tree is a **table** `ω`. A random table is the source of *all* the
randomness of *all* programs.

### The Lean

```lean
abbrev Addr := List ℕ                                    -- a node of the tree: its path
abbrev Table := Addr → I                                 -- I = unitInterval = [0,1]
def U : Measure Table := Measure.infinitePi fun _ ↦ volume   -- all entries iid uniform
```

([`U`, line 92](../Test/RandomSource.lean#L92)). `Measure.infinitePi` is Mathlib's product of
arbitrarily many probability measures, and `U` is a probability measure.

**Zooming in.** [`subAt pre ω`](../Test/RandomSource.lean#L97) is the subtree of `ω` rooted at
`pre`, renamed so that its root is `[]` again:

```lean
def subAt (pre : Addr) (ω : Table) : Table := fun a ↦ ω (pre ++ a)
```

Picture: put a magnifying glass on node `pre`, and what you see is again a whole tree.

Three facts about the table are used all the time.

* [`map_subAt`](../Test/RandomSource.lean#L104): `U.map (subAt pre) = U`. *Zooming into a random
  table gives a random table.* The entries under `pre` are still iid uniform. (Proof: it is a
  reindexing by the injective map `a ↦ pre ++ a`, which is Mathlib's
  `map_infinitePi_infinitePi_of_inj`.)
* [`map_eval`](../Test/RandomSource.lean#L112): `U.map (fun ω ↦ ω a) = volume`. *A single entry is
  uniform.*
* `dependsOn_subAt`: `subAt pre` only looks at the entries whose address starts with `pre`
  (`pre <+: a` means "`pre` is a prefix of `a`").

### Why it is there

The table is the probability space. Everything that follows is a random variable on `(Table, U)`.

---

## 2. Independence: reading disjoint entries

### The picture

Imagine two people, each allowed to look at only some of the entries of the table, and each
computing something from what they see. If no entry is seen by both, their results are
independent. That is the only independence fact the file uses.

### The Lean

"Only looks at the entries in `S`" is Mathlib's `DependsOn F S`:

```lean
DependsOn F S  :=  ∀ ω ω', (∀ a ∈ S, ω a = ω' a) → F ω = F ω'
```

Picture: `F` wears blinkers that let it see only the cells in `S`.

[`indepFun_of_dependsOn`](../Test/RandomSource.lean#L160):

```lean
theorem indepFun_of_dependsOn (hF : Measurable F) (hG : Measurable G)
    (hFS : DependsOn F S) (hGT : DependsOn G T) (hST : Disjoint S T) : IndepFun F G U
```

*(proof, skippable)*

1. The entries `ω ↦ ω a` are mutually independent under `U`: this is
   [`iIndep_entries`](../Test/RandomSource.lean#L153), from Mathlib's `iIndepFun_infinitePi`.
2. Mathlib's `indep_iSup_of_disjoint` groups them: the σ-algebra generated by the entries in `S` is
   independent of the one generated by the entries in `T`.
3. What remains is to show that `F` is measurable for the σ-algebra of the entries in `S`
   ([`comap_le_iSup`](../Test/RandomSource.lean#L138)). `DependsOn` alone does not give that.
   The trick: blank out every entry outside `S` with a `0` (`fill`). This does not change `F`
   (that is `DependsOn`), and it writes `F` as a measurable function of the entries in `S` only.

### Why it is there

Every law, conditional law and independence statement later in the file reduces to this theorem.

---

## 3. From a uniform number to a draw: samplers

### The picture

Given a Markov kernel `κ : Kernel γ α`, a **sampler** is a machine that takes a parameter `c` and
one uniform number `u ∈ [0,1]`, and outputs a draw from `κ c`. For `α = ℝ` you can think of it as
the inverse CDF (quantile function) of `κ c`, evaluated at `u`.

### The Lean

Mathlib provides exactly this, as `Kernel.exists_measurable_map_eq_unitInterval` (Kallenberg,
Lemma 4.22). When `α` is a standard Borel space, there is a jointly measurable
`f : γ → I → α` with `volume.map (f c) = κ c` for every `c`. The file names one such map:

```lean
def sampler (κ : Kernel γ α) [IsMarkovKernel κ] : γ → I → α    -- chosen with Classical.choice
lemma measurable_sampler : Measurable (uncurry (sampler κ))
lemma map_sampler : volume.map (sampler κ c) = κ c
```

([`sampler`, line 195](../Test/RandomSource.lean#L195)). Combined with `map_eval`:

[`hasLaw_sampler κ c a`](../Test/RandomSource.lean#L217): `HasLaw (fun ω ↦ sampler κ c (ω a)) (κ c) U`.
*Reading entry `a` through the sampler gives a draw from `κ c`.*

A sampler is *chosen*, so we never know what it is, only its law. Two different kernels get
unrelated samplers, even kernels that agree at some point.

### Why it is there

Samplers are how programs turn table entries into values (section 4).

---

## 4. Programs that read the table: the monad `Src`

### The picture

A program becomes a deterministic machine: hand it a table, and it produces a value.

```lean
abbrev Src (α : Type) [MeasurableSpace α] : Type := Table → α
```

([line 173](../Test/RandomSource.lean#L173)). The only design decision is *which entries each part
of the program gets to read*. The answer is the monad structure
([line 177](../Test/RandomSource.lean#L177)):

```lean
instance : MeasurableSpaceMonad Src where
  mPure a    := fun _ ↦ a
  mBind p q  := fun ω ↦ q (p (subAt [0] ω)) (subAt [1] ω)
```

* `return a` ignores the table.
* `let x ← p; q x` **splits the tree at the root**. `p` runs on the subtree under `[0]`. The
  continuation `q x` runs on the subtree under `[1]`.

Nothing is "consumed" or threaded along, unlike a random-seed state monad: parts of the table are
handed out *by position in the program*.

A draw needs one more operation, `sample`, provided by a small class
([`HasSample`, line 182](../Test/RandomSource.lean#L182)):

```lean
class HasSample (m) where
  sample (κ : Kernel γ α) [IsMarkovKernel κ] (c : γ) : m α
```

* At `m := Measure`: `sample κ c := κ c`.
* At `m := Src`: `sample κ c := fun ω ↦ sampler κ c (ω [])`, i.e. a draw **reads the root entry
  of the part of the table it was handed**.

### Working out addresses

Take the program above. `rdo` elaborates it to

```lean
draw μ >>=ₘ fun x ↦ (draw μ >>=ₘ fun y ↦ mPure (x + y))
```

* The first `draw` is the left side of the outer bind, so it gets `subAt [0] ω`. It reads that
  subtree's root, i.e. **`ω [0]`**.
* The continuation gets `subAt [1] ω`. Inside it, the second `draw` is the left side of the inner
  bind, so it gets `subAt [0] (subAt [1] ω)` and reads **`ω [1, 0]`**.
* `mPure` reads nothing.

**Rule of thumb:** a draw's address is the sequence of `0`s and `1`s picked up through the binds
around it (`0` for "I am the first half of this bind", `1` for "I am in its continuation"),
followed by nothing at all, because a draw reads the root of its part.

**The fact that makes everything work.** Two different draws never read the same entry. Follow
their addresses from the root: they separate at the bind that separates them, where one goes to
`0` and the other to `1`. Loops and recursive calls are, once unrolled, just more binds, so this
holds for them too, and nothing special is needed for them.

Many entries are never read (`[]`, `[1]`, `[1, 1]`, …). That is wasteful but harmless.

### Why it is there

Running a program at `m := Src` gives a random variable on the table for its result, and for
every draw inside it, since each draw is "the sampler applied to one known entry".

---

## 5. Writing programs once, for two monads

### The picture

One recipe, two kitchens. The same `rdo` program is written once, for an arbitrary monad `m` with
`[MeasurableSpaceMonad m] [HasSample m]`:

* in the `Measure` kitchen it computes a **distribution**, the usual meaning of an `rdo` program;
* in the `Src` kitchen it computes an **outcome from a table**.

This is the pattern the repository already uses in `Polymorphic.lean` (programs run at `RandM`)
and in `Bandits/Defs.lean` (`banditRunRand (m := Measure)`).

### The Lean

For fixed distributions there is a convenience wrapper
([`draw`, line 515](../Test/RandomSource.lean#L515)):

```lean
def draw (μ : Measure α) [IsProbabilityMeasure μ] : m α := HasSample.sample (Kernel.const Unit μ) ()
```

The first example is ([line 553](../Test/RandomSource.lean#L553)):

```lean
def sumTwo : m ℝ := rdo
  let x ← draw (gaussianReal 0 1)
  let y ← draw (gaussianReal 0 1)
  return x + y
```

`sumTwo (m := Measure)` is the usual measure. `sumTwo (m := Src)` is a function of the table.

### Why it is there

To say anything probabilistic about the `Src` version, we have to know that its law is the
`Measure` version. That is the next section.

---

## 6. `Realizes`: the two kitchens agree

### The picture

"Feed random tables to the machine, and look at the distribution of what comes out: it is the
`Measure` program."

### The Lean

[`Realizes`, line 236](../Test/RandomSource.lean#L236), for families of programs with a parameter
`c : γ`:

```lean
structure Realizes (p : γ → Src α) (μ : γ → Measure α) : Prop where
  measurable : Measurable fun x : γ × Table ↦ p x.1 x.2     -- jointly measurable
  map_eq (c : γ) : U.map (p c) = μ c                          -- the law of p c is μ c
```

**Why it has to be proved program by program.** `sumTwo (m := Src)` and `sumTwo (m := Measure)`
are the same definition used at two monads, but Lean cannot conclude from that alone that they
"do the same thing". That would be a *parametricity* theorem, which Lean cannot prove internally.
So `Realizes` is proved construct by construct, with one lemma per construct:

| construct | lemma | what it needs |
|---|---|---|
| `return g c` | [`Realizes.pure`](../Test/RandomSource.lean#L281) | `g` measurable |
| `sample κ c` | [`Realizes.sample`](../Test/RandomSource.lean#L293) | `hasLaw_sampler` at `[]` |
| `draw μ` | [`Realizes.draw`](../Test/RandomSource.lean#L521) | the above, constant parameter |
| `p (g d)` | `Realizes.comp` | reparametrization, `g` measurable |
| `let x ← p c; q c x` | [`Realizes.bind`](../Test/RandomSource.lean#L312) | `p` realized, and `q` realized as a family over `γ × α` |
| `if P c then … else …` | [`Realizes.ite`](../Test/RandomSource.lean#L349) | `{c | P c}` measurable |
| `for a in l …` | [`Realizes.forIn`](../Test/RandomSource.lean#L498) | the body realized, for each element |

**The bind case** is the only one with probabilistic content.
*(proof, skippable)*

1. [`map_split`](../Test/RandomSource.lean#L302): `(subAt [0] ω, subAt [1] ω)` has law `U ⊗ U`.
   The two halves of a random table are independent random tables (section 2 plus `map_subAt`).
2. So running `p` on the left half and `q` on the right half is "draw `x` from the law of `p`,
   then, independently, run `q x`". That is `μ >>=ₘ ν` at `Measure`, and
   [`map_prod_eq_compProd'`](../Test/RandomSource.lean#L260) is the Fubini-type computation
   saying so: `(μ.prod ν).map (x, f x y) = μ ⊗ₘ κ` when `f x` pushes `ν` to `κ x`.

**The law as a kernel.** For a jointly measurable family `p`,
[`lawK p`](../Test/RandomSource.lean#L241) is the Markov kernel `c ↦ U.map (p c)`, and
`Realizes.lawK_eq` says that `lawK p = κ` when `p` realizes `κ`.

**Loops.** `rdo`'s `for` over a list is implemented, for any monad, in
`RandomDo/Monad/ForInInstances.lean` by an auxiliary `let rec`. The file restates it as a plain
structural recursion, [`listLoop`](../Test/RandomSource.lean#L441):

```lean
listLoop g []       b = mPure b
listLoop g (a :: l) b = g a b >>=ₘ fun step ↦ match step with
                          | done b'  => mPure b'
                          | yield b' => listLoop g l b'
```

and [`forIn_eq_listLoop`](../Test/RandomSource.lean#L466) proves that the two agree, for any
monad. So a loop is "run the body, then stop or carry on", which is a bind followed by a branch,
and [`Realizes.listLoop`](../Test/RandomSource.lean#L480) is an induction on the list using
`Realizes.bind` and `Realizes.ite`.

Consequence for addresses: iteration `k` of a loop runs under `1ᵏ ++ [0]` of the loop's own part.
The first iteration is the left half, the rest of the loop is the right half, and so on.

**The `realize` tactic** ([line 529](../Test/RandomSource.lean#L529)) tries these lemmas
repeatedly and discharges side conditions with `fun_prop` and `measurability`. It plays the role
`is_markov` and `rdo_trace` play elsewhere, but its job is much smaller: it only proves that the
laws match. The random variables themselves need no tactic, since they are just what the `Src`
program computes.

### Why it is there

`Realizes` connects outcomes on the table to the laws LeanMachineLearning speaks about (kernels,
`Algorithm.policy`, …). It also gives the law of each program's result.

---

## 7. The key lemma: fresh randomness

### The picture

Let `C` be "everything that has happened so far", as a random variable on the table. It only
looked at some entries. Now run a program `q`, with parameter `C`, on a part of the table that `C`
never looked at. Then, *given* `C`, the result behaves exactly like the program `q` at the
parameter `C`. The randomness it uses is fresh.

### The Lean

[`hasCondDistrib_fresh`, line 374](../Test/RandomSource.lean#L374):

```lean
theorem hasCondDistrib_fresh (hC : Measurable C) (hCS : DependsOn C S)
    (hpre : ∀ a ∈ S, ¬ pre <+: a)                      -- C never looks under `pre`
    (hq : Measurable fun x : X × Table ↦ q x.1 x.2) :
    HasCondDistrib (fun ω ↦ q (C ω) (subAt pre ω)) C (lawK q) U
```

`HasCondDistrib Y C κ U` says that the conditional law of `Y` given `C` is `κ`. By definition, it
means that `(C, Y)` has law `(law of C) ⊗ₘ κ`.

*(proof, skippable)* `C` and `subAt pre` are independent (section 2), and `subAt pre` has law `U`.
So `(C, subAt pre)` has law `(law of C) ⊗ U`, and `map_prod_eq_compProd'` finishes.

There are three variants of the same statement:

* `hasCondDistrib_fresh'`: the same, when `q` realizes a known kernel `κ` (so the conclusion
  mentions `κ` rather than `lawK q`).
* [`hasCondDistrib_entry`](../Test/RandomSource.lean#L402): the single-entry version. For
  `f : X → I → α` with `volume.map (f x) = κ x`, and an entry `a ∉ S`,
  `HasCondDistrib (fun ω ↦ f (C ω) (ω a)) C κ U`.
* `hasCondDistrib_sampler`: the single-entry version with `f := sampler κ`.

### Why it is there

This replaces all the "peeling" of `Trace.lean`. There, conditional laws came from the *shape* of
the trace kernel, a nested `⊗ₖ`. Here they come from *which entries were read*. The shape of the
program never matters, only this bookkeeping of entries. That is why branches, loops and the
interaction with an environment need no special treatment.

---

## 8. Example 1: two independent draws (`§ Example 1`)

The program is `sumTwo` (section 5). Reading off its addresses (section 4), the random variables
are

```lean
abbrev gauss : I → ℝ := sampler (Kernel.const Unit (gaussianReal 0 1)) ()   -- the sampler `draw` uses
def X (ω : Table) : ℝ := gauss (ω [0])
def Y (ω : Table) : ℝ := gauss (ω [1, 0])
```

* `sumTwo_src : sumTwo (m := Src) ω = X ω + Y ω`, proved by **`rfl`**. The program literally
  computes `X + Y`, by unfolding the definitions.
* `hasLaw_X`, `hasLaw_Y`: each is `hasLaw_sampler` at its address.
* `indepFun_X_Y`: `indepFun_of_dependsOn` with the singletons `{[0]}` and `{[1, 0]}`.
* `realizes_sumTwo`: `unfold sumTwo; realize`.
* `hasLaw_X_add_Y`: `X + Y` has law `sumTwo (m := Measure)`.

Together: the program is the law of the sum of two independent standard Gaussians, which is
exactly what one means by the program text.

---

## 9. Example 2: a chain of dependent draws (`§ Example 2`)

This is `chain` of `RandomDo/Probability/Examples.lean`, written for any monad:

```lean
def chain (c : ℝ) : m ℝ := rdo
  let x ← sample κ c              -- reads [0]
  let y ← sample η (c, x)         -- reads [1, 0]
  let z ← sample θ ((c, x), y)    -- reads [1, 1, 0]
  return x + y + z
```

The random variables compute each draw from its own entry and from the draws before it:

```lean
def CX ω := sampler κ c (ω [0])
def CY ω := sampler η (c, CX ω) (ω [1, 0])
def CZ ω := sampler θ ((c, CX ω), CY ω) (ω [1, 1, 0])
```

* `hasLaw_CX`: `CX` has law `κ c`.
* `hasCondDistrib_CY`: *given `CX`*, `CY` has law `η (c, ·)`. This is `hasCondDistrib_fresh'`
  with `C := CX`, which reads `{[0]}`, and the fresh part `[1, 0]`.
* `hasCondDistrib_CZ`: *given `(CX, CY)`*, `CZ` has law `θ ((c, ·), ·)`. The same lemma, with
  `S := {[0], [1, 0]}` and the fresh part `[1, 1, 0]`.
* `hasLaw_chain`: the result has the law of the program.

Compare the by-hand peeling of the same program in `Examples.lean`, section *A dependent chain*.
Here each conditional law is one application of one lemma.

---

## 10. Example 3: a loop with a branch (`§ Example 3`)

```lean
def coinSum (n : ℕ) : m ℝ := rdo
  let mut S := 0
  for _ in List.replicate n () rdo
    let b ← draw fairCoin
    if b then
      let z ← draw (gaussianReal 0 1)
      S := S + z
  return S
```

([line 696](../Test/RandomSource.lean#L696)). The number of Gaussians actually drawn is random.
This is exactly the kind of program a trace built from the program's shape struggles with.

### Addresses

* The whole program is `forIn … >>=ₘ fun S ↦ mPure S`, so the loop sits under **`[0]`**.
* Iteration `k` of the loop sits under `1ᵏ ++ [0]` of the loop's part (section 6), i.e. under
  **`0 :: 1ᵏ ++ [0]`** of the table.
* Inside an iteration, the coin is the first half of a bind, **`[0]`**. The Gaussian is in the
  continuation, then the first half of the inner bind: **`[1, 0]`**.

[`iterAddr k t = 0 :: (1ᵏ ++ 0 :: t)`](../Test/RandomSource.lean#L750) packages this, and

```lean
def B (k : ℕ) (ω : Table) : Bool := coin  (ω (iterAddr k [0]))      -- the coin of iteration k
def Z (k : ℕ) (ω : Table) : ℝ    := gauss (ω (iterAddr k [1, 0]))   -- the Gaussian of iteration k
```

### Draws in a branch not taken still exist

`Z k` is defined for *every* table, including those where `B k` says tails. The program simply
does not look at that entry. So the branch turns into a multiplication by an indicator:

[`coinSum_src`](../Test/RandomSource.lean#L770): `coinSum (m := Src) n ω = ∑ k < n, if B k ω then Z k ω else 0`.

(Its proof is an induction over the loop. It uses `coinBody`, the loop body restated as `rdo`
elaborates it, `coinSum_eq`, which holds by `rfl`, and `forIn_coinBody`, which generalizes the
initial value of `S`.)

### Conditional laws

* `Past k` collects `(B j, Z j)` for `j < k`, and `pastAddrs k` is the set of entries iterations
  `j < k` may read. `iterAddr_inj` says different iterations use disjoint addresses.
* [`hasCondDistrib_B`](../Test/RandomSource.lean#L797): given the past, the coin of iteration `k`
  is fair.
* [`hasCondDistrib_Z`](../Test/RandomSource.lean#L803): given the past *and the coin*, `Z k` is
  standard Gaussian. This holds even on the event where the branch is not taken, because the entry
  is there either way. As a corollary (an `example` in the file), `Z k` is independent of
  `(Past k, B k)`.
* `hasLaw_coinSum`: `∑ 1{B k} Z k` has the law of the program.

No case analysis on the branch appears anywhere.

---

## 11. Example 4: an algorithm interacting with an environment (`§ Example 4`, namespace `Interaction`)

### 11.1 Algorithms and environments as table programs

[`SrcAlg`](../Test/RandomSource.lean#L857) and `SrcEnv` hold, for every round `n`, a table program
computing:

* for the algorithm: the action, from the history and the current observation;
* for the environment: the observation, from the history; and the feedback, from the history, the
  observation and the action;

together with joint measurability. Their laws (`lawK`) make them a LeanMachineLearning
`Algorithm` and `Environment` (`SrcAlg.toAlgorithm`, `SrcEnv.toEnvironment`). When the program
realizes a known kernel, `SrcAlg.toAlgorithm_policy` says that this kernel is the policy.

### 11.2 The layout of the table

**Round `n` reads the subtree under `[n]`**: the observation under `[n, 0]`, the action under
`[n, 1]`, the feedback under `[n, 2]`.

* [`playRound n h ω`](../Test/RandomSource.lean#L892) plays one round given the history `h`.
* [`round n ω`](../Test/RandomSource.lean#L898) is round `n` of the interaction, defined by
  well-founded recursion from rounds `0, …, n-1`.
* `O n`, `A n`, `Y n` are its three components, and `H n` is LeanMachineLearning's
  `history O A Y n`. `H_apply` says that this history is `(round 0, …, round (n-1))`, by `rfl`.
* `O_eq`, `A_eq`, `Y_eq` unfold one round. For example, `A n ω` is the policy program, run on
  `(H n ω, O n ω)` and on the part `subAt [n, 1] ω`.

**Why rounds are placed by hand at `[n]`.** One could instead write the interaction as an `rdo`
recursion, like `banditRunRand (n+1) = banditRunRand n >>= step`. Under the bind rule, round `t`
would then sit under a path whose length depends on the total number of rounds `n`. But
`IsAlgEnvSeq` needs a single random variable `A t` that works for every horizon. Indexing rounds
by their number avoids the problem.

### 11.3 The bookkeeping of entries

* [`before n`](../Test/RandomSource.lean#L954): the entries rounds `0, …, n-1` may read (addresses
  starting with some `j < n`).
* `part n i`: the entries under `[n, i]`.
* `dependsOn_round`, `dependsOn_H`, `dependsOn_HO`, `dependsOn_HOA`: the history reads only
  `before n`; the history and the observation read `before n ∪ part n 0`; adding the action adds
  `part n 1`.
* `not_prefix_before`, `not_prefix_part`: the part under `[n, i]` is fresh for those sets.

### 11.4 The theorem

[`isAlgEnvSeq`, line 1007](../Test/RandomSource.lean#L1007):

```lean
theorem isAlgEnvSeq :
    IsAlgEnvSeq (O alg env) (A alg env) (Y alg env) alg.toAlgorithm env.toEnvironment U
```

Its three conditional-law fields are three applications of `hasCondDistrib_fresh`: the
observation reads `[n, 0]`, which the history never reads; the action reads `[n, 1]`, which
neither the history nor the observation read; and so on. The proof never looks inside the
programs, so it holds for **any** algorithm and environment given by table programs, with any
branches, loops or recursion inside a round.

### 11.5 ε-greedy

A concrete instance, with two arms (`Bool`) and Gaussian rewards:

```lean
def epsPolicy (n : ℕ) (x : Hist Unit Bool ℝ n × Unit) : m Bool := rdo
  let explore ← draw (bernoulliMeasure true false ε)
  if explore then
    let u ← draw fairCoin
    return u
  else
    return lastAction n x.1
```

* `realizes_epsPolicy`: `unfold epsPolicy; realize`.
* `epsAlg`, `gaussEnv`: the algorithm and the environment as table programs.
  [`epsAlg_policy`](../Test/RandomSource.lean#L1092) says that the LeanMachineLearning policy *is*
  the `rdo` program at `Measure`.
* `isAlgEnvSeq_eps`: the general theorem, applied.

**The internal draws are random variables on the same space.** The policy of round `t` runs under
`[t, 1]`, so:

* `Explore t` reads `[t, 1, 0]`, the first half of the policy's bind;
* [`Unif t`](../Test/RandomSource.lean#L1110) reads **`[t, 1, 1]`**, not `[t, 1, 1, 0]` as one
  might expect. `rdo` elaborates `let u ← draw fairCoin; return u` to just `draw fairCoin`, which
  removes a bind. Addresses follow the *elaborated* program. This is the main practical subtlety
  of the approach (see the limitations).

Then:

* [`A_eps`](../Test/RandomSource.lean#L1113), pathwise:
  `A t ω = if Explore t ω then Unif t ω else lastAction t (H t ω)`.
* [`hasCondDistrib_Explore`](../Test/RandomSource.lean#L1122): given the history and the
  observation, round `t` explores with probability `ε`.
* [`le_map_A`](../Test/RandomSource.lean#L1134): every arm is played with probability at least
  `ε · fairCoin {a}`, i.e. `ε/2` (the file leaves `fairCoin {a}` as it is). The proof reads it off `A_eps`. The event
  `{Explore t} ∩ {Unif t = a}` is contained in `{A t = a}`, and its two parts read two different
  entries, so they are independent.
* [`le_map_action`](../Test/RandomSource.lean#L1159): **the same bound for every
  `IsAlgEnvSeq` of ε-greedy, on any probability space.** LeanMachineLearning's
  `isAlgEnvSeq_unique` says that the law of the trajectory does not depend on the space, and
  `A t` is a function of the trajectory.

Compare `Bandits/EpsGreedy.lean`. There, `alg_env_trace` *extends* an arbitrary space with the
draws of the policy. Here, the draws come for free on one canonical space, and results are moved
to other spaces when they only involve the trajectory.

---

## 12. The two approaches side by side

| | `Trace.lean` / `rdo_trace` / `rdo_peel` | `RandomSource.lean` |
|---|---|---|
| probability space | built per program, shaped like it (`⊗ₖ` of the draws) | one table of iid uniforms, for all programs |
| what a draw is | a coordinate of the trace space | a sampler applied to one entry of the table |
| where conditional laws come from | the nesting of `⊗ₖ` (peeling) | which entries were read (`hasCondDistrib_fresh`) |
| branches | the whole rest of the program becomes one atomic coordinate | free: a draw not taken is still a random variable |
| loops | not decomposed | free: iteration `k` has its own part of the table |
| algorithm-environment sequences | `AlgTrace`, extending a given space | `Interaction.isAlgEnvSeq`, on the table, then transfer |
| what needs automation | building the trace and peeling it | proving `Realizes` (`realize`) and, not yet done, reading off addresses |

---

## 13. Limitations

These are listed roughly from the most to the least consequential.

1. **The random variables are written by hand.** `X`, `Y`, `B k`, `Z k`, `Explore t`, `Unif t` are
   all defined by reading off the address of each draw, as in section 4. Those addresses follow
   the *elaborated* program, not its text (see `Unif`, section 11.5). They also move when the
   program is edited: inserting a `←` before a draw shifts the addresses of everything after it.
   The statements about *laws* survive such changes; only the definitions of the variables break.
   A tactic or metaprogram reading the addresses off the elaborated term is the natural next step.
   Another option is a variant of `Src` that also records the value drawn at each address.

2. **Programs have to be written for a generic monad with `sample`/`draw`.** A program written
   directly at `Measure`, like the original `sumTwo`, is not covered, and neither is one using a
   parametrized distribution as a leaf (`let y ← gaussianReal x 1`). Such a leaf has to be
   packaged as a Markov kernel and drawn with `sample`. On the other hand, any subprogram known to
   be Markov can be drawn as one atomic `sample` from its kernel. That is the same granularity knob
   as in `rdo_trace`.

3. **`realize` only covers `return`, `←`, `if`, `for` over a list, `sample` and `draw`.** Not yet
   covered: `match`, `dite`, early `break`/`return` inside a loop (`Break.runK`), loops over
   arrays and vectors, and loops over a list that depends on the parameter. Each needs a
   `Realizes` lemma in the style of `Realizes.ite` and `Realizes.forIn`. They are straightforward,
   but they are not written.

4. **The bookkeeping of entries is done by hand.** Every conditional-law statement needs a
   `DependsOn` proof and a disjointness proof (`pastAddrs`, `iterAddr_inj`, `before`, `part`, the
   `not_prefix_*` lemmas). This is routine and could be automated, since the sets involved are
   always unions of subtrees, but for now it is the bulk of the proofs.

5. **The interaction loop is written by hand.** `round` places round `n` at `[n]`, and the
   algorithm and environment must be given per round, as `SrcAlg`/`SrcEnv`. An interaction
   written as an `rdo` recursion over the horizon would have horizon-dependent addresses (section
   11.2), so it would need either a different layout for recursion or a lemma relating the two.

6. **Results about internal draws live on the table only.** `le_map_action` transfers to any
   space because it is a statement about the trajectory. A statement mentioning `Explore t` itself
   does not transfer: on another space, the exploration coin simply does not exist. That is the
   job `alg_env_trace` does, by extending the space, so the two approaches are complementary.

7. **Samplers are chosen, not computed.** `sampler` comes from `Classical.choice`, so `Src`
   programs cannot be executed, and pathwise statements are about an unknown sampler. Only
   statements about laws are meaningful. Samplers of different kernels are unrelated. For
   instance, `hasCondDistrib_B` has to use `hasCondDistrib_entry` with `f := fun _ u ↦ coin u`,
   because the coin's sampler is that of `Kernel.const Unit fairCoin`, not of a kernel over
   `Past k`.

8. **Value types must be standard Borel (and nonempty),** because of the sampler lemma. That covers
   `ℝ`, `Bool`, `Fin K`, vectors and finite products. Also, everything is at `Type` (universe 0),
   like the `m : (α : Type) → … → Type` of `HasSample`.

9. **Only pairwise and conditional independence are packaged.** There is no lemma giving mutual
   independence (`iIndepFun`) of variables that read pairwise disjoint *sets* of entries. Example
   3 states conditional laws instead. Mathlib's `indep_iSup_of_disjoint` groups entries into two
   independent blocks, but I did not find the version for a family of blocks.

10. **Loop addresses grow with the iteration number.** Iteration `k` lives at depth `k + 2`, which
    is why `List.replicate k 1` shows up in Example 3. A custom `for` instance for `Src` could put
    iteration `k` directly under `[k]`, at the cost of proving its own `Realizes` lemma.

11. **It is a prototype.** It is a single file in `Test/`, with short names (`X`, `Y`, `B`, `Z`, `O`,
    `A`, `Y`, …) that only make sense inside their sections, and no attempt at an API.

---

## 14. Cheat sheet

| name | meaning |
|---|---|
| `Addr`, `Table`, `U` | addresses (paths in a tree), tables, and the law of a random table |
| `subAt pre ω` | the subtree of `ω` under `pre`, re-rooted |
| `DependsOn F S` | `F` only looks at the entries in `S` |
| `indepFun_of_dependsOn` | disjoint entries ⇒ independent |
| `sampler κ c u` | a draw from `κ c` made from the uniform number `u` |
| `Src α` | a program as a function of the table |
| `mBind` at `Src` | the first half of the bind reads under `[0]`, the continuation under `[1]` |
| `sample`, `draw` | a draw reads the root entry `[]` of its part |
| `Realizes p μ` | pushing `U` through `p c` gives `μ c` |
| `lawK p` | the kernel `c ↦ U.map (p c)` |
| `realize` | proves `Realizes` construct by construct |
| `hasCondDistrib_fresh` | a program run on an unread part has, given what was read, the program's law |
| `hasCondDistrib_entry` | the same, for a single entry |
| `SrcAlg`, `SrcEnv` | an algorithm and an environment given by table programs, per round |
| `round n` | round `n` of the interaction; it reads under `[n]`: obs `[n,0]`, action `[n,1]`, feedback `[n,2]` |
| `Interaction.isAlgEnvSeq` | the interaction on the table is an `IsAlgEnvSeq` |
