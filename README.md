# Random-do notation

RandomDo writes probabilistic algorithms in `rdo`. The same program can be interpreted as a
mathematical measure for proofs or instantiated with an executable sampling backend.

## Differential privacy

Import `RandomDo` (or `RandomDo.DifferentialPrivacy`) and open `DifferentialPrivacy`.

### The Gaussian `rdo` samplers

The algorithms are in [`RandomDo/DifferentialPrivacy/Programs.lean`](RandomDo/DifferentialPrivacy/Programs.lean):

- `gaussianProgram center σ` draws zero-mean Gaussian noise and returns `center + noise`.
- `gaussianCoordinates center σ` does this independently for each coordinate.
- `gaussianMeanRealProgram f D c n xs` computes the scalar empirical mean and adds noise.
- `gaussianMeanProgram f D c n xs` computes the vector empirical mean and adds independent noise
  in each coordinate.

The full scalar mean algorithm is:

```lean
def gaussianMeanRealProgram {α : Type*} {R V : Type} [Scalar R] [Scalar V]
    [HasGaussian m R V R] (f : α → R) (D c : V) (n : ℕ) (xs : Dataset α) : m R := rdo
  let center := meanValue f xs
  let σ := c * D / (n : V)
  let z ← gaussianProgram (m := m) center σ
  return z
```

Here `m` is an arbitrary `MeasurableSpaceMonad`. `meanValue` is pure arithmetic, and
`gaussianProgram` samples through `HasGaussian` in `rdo`. The vector version uses the same
computation coordinatewise. There is one implementation of each algorithm.

`D` is a public upper bound on the domain's ℓ₂ diameter, `n > 0` is a public lower bound on
sample size, and `c` is a public noise multiplier. The standard deviation is `c * D / n`;
`HasGaussian` takes **variance**, so the sampler passes its square.

At `m := Measure`, `R := ℝ`, and `V := ℝ≥0`, the programs denote exact real distributions.
The theorems `gaussianMeanRealProgram_eq_mechanism` and `gaussianMeanProgram_eq_mechanism`
identify these complete programs with the Gaussian laws used in the privacy proofs.
Choosing another interpretation runs these same definitions. The existing floating-point
backend is exercised in `Test.DifferentialPrivacy`; its arithmetic and generator are not part
of the exact-real privacy guarantee.

### Privacy of the programs

The following proves privacy of the actual vector `rdo` sampler under adding or removing one
record. `Mechanism.ofMeasure` only pairs the program with its proof of total probability one.

```lean
import RandomDo

open DifferentialPrivacy MeasureTheory
open scoped NNReal

example {α : Type*} {d : ℕ} (f : α → EuclideanSpace ℝ (Fin d))
    {D ε δ : ℝ≥0} (hD : HasDiameter f D)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ApproxDP (Dataset.AtLeast 10 Dataset.AddRemove) ε δ
      (Mechanism.ofMeasure
        (gaussianMeanProgram (m := Measure) (fun a ↦ ⇑(f a)) D
          (gaussianNoiseMultiplier ε δ) 10) (fun _ ↦ inferInstance)) :=
  gaussianMeanProgram_approxDP_addRemove hD (by norm_num) hε hδ hδ1
```

`gaussianMeanProgram_approxDP_replaceOne` covers replacement. The corresponding scalar theorems
are prefixed `gaussianMeanRealProgram_approxDP`. Zero diameter is supported and requires no noise.

For `ε > 0` and `0 < δ ≤ 1`, `gaussianNoiseMultiplier ε δ` supplies the multiplier:

```text
t = sqrt(2 log(1/δ))
c = (t + sqrt(t² + 2ε)) / (2ε)
σ = c * D / n
```

This sufficient calibration follows from a Gaussian Chernoff bound and works for every positive
`ε`. The proof establishes the joint density ratio, a dimension-independent directional tail
bound, and the DP event inequality. See
[Dwork and Roth, Appendix A](https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf) for the
Gaussian privacy-loss argument; this calibration solves the Chernoff inequality directly.

### Theory and assumptions

- `Dataset α` is `List α`: finite sequences of arbitrary length, allowing repeated records.
- `Dataset.AddRemove` inserts or removes one record at any position; `Dataset.ReplaceOne`
  replaces one record while preserving length.
- `Mechanism X Y` maps inputs to `ProbabilityMeasure Y`.
- `PureDP adj ε M` means `P(M x ∈ A) ≤ exp(ε) P(M x' ∈ A)` for adjacent inputs and
  measurable output events.
- `ApproxDP adj ε δ M` adds `δ` to the right-hand side. Nonconstant Gaussian releases generally
  require this approximate notion.

The theory includes measurable deterministic postprocessing, restriction of adjacency,
adjacency-preserving input transformations, and monotonicity in privacy budgets.

`HasDiameter f D` bounds all pairs of records in the public domain. For vectors, use an embedding
into `EuclideanSpace ℝ (Fin d)` to express the ℓ₂ norm. A bound on each coordinate alone is not an
ℓ₂ diameter bound. If both datasets have at least `n > 0` records, the empirical mean has
sensitivity at most `D / n` under either adjacency relation. Inserting into a nonempty dataset
has the sharper bound `D / (length + 1)`.

The programs accept their parameters directly; the privacy theorems state the conditions on
those parameters and the inputs. `n` and `D` must be public. Choosing the variance from the
private dataset size or its observed diameter is not justified by these theorems. The real mean
of an empty list is defined as zero, but the mean privacy theorems require nonempty datasets.

Run the library, proofs, and execution checks with `lake build RandomDo Test`.
