# Random-do notation

Write a probability program once using `rdo`, then interpret it in different measurable-space
monads. `Measure` gives its distribution; `RandomM Ω P` samples from a probability source while
preserving fresh source state. `SampleM Ω P` uses an infinite stream of independent `P` draws.

To relate the two interpretations, add `rdo_program` to a polymorphic definition:

```lean
import RandomDo

open MeasureTheory
universe v

def sumDraws {m : (α : Type) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] (coin : m Bool) : ℕ → m ℕ
  | 0 => rdo return 0
  | n + 1 => rdo
    let b ← coin
    let s ← sumDraws coin n
    return b.toNat + s

attribute [rdo_program] sumDraws

example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (coin : RandomM Ω P Bool) (n : ℕ) :
    (sumDraws coin n).law = sumDraws (m := Measure) coin.law n :=
  sumDraws.law coin n
```

The attribute leaves the original definition unchanged. It generates a recorded program
(`.program`), a certificate (`.valid` and `.certified`), bridges to the original interpretations
(`.sample_bridge` and `.measure_bridge`), and the resulting `.law` theorem. The proof uses
`RDo.Program.Certified.law`, which holds for every certified program. The `rdo_valid` tactic can
also construct certificates directly, leaving any unresolved measurability conditions as goals.

The current automation supports returns, binds, measurable conditionals, sampler arguments,
and one-argument sampler families. A family argument adds a joint-measurability hypothesis to
the generated certificate and law theorem. `SampleM.ofKernel` provides this property for Markov
kernels; `SampleM.ofMeasure` supplies independent draws from probability measures on standard
Borel spaces. Both constructors use a stream of uniform draws from the unit interval.

The attribute currently requires leading `{m} [MeasurableSpaceMonad m]` parameters and an
independent universe parameter for the monad's output, as above. It attempts induction on the
last explicit `Nat` argument. General recursion and loops need further support. Certification
fails if a proof obligation remains; no global measurable-evaluation assumption is required.

See `Test/Program.lean` for continuous and kernel examples, and `Test/SampleM.lean` for independent
draws and the proof that a sum of `n` Bernoulli samples has the binomial distribution.
