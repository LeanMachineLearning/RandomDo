/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Gaëtan Serré
-/
module

public import RandomDo.Sampling.WithSampling
public import RandomDo.WP.MeasurableSpaceMonad

/-!
# Weakest preconditions of named sampling interpretations

A sampling tag changes the choice of primitive instances, while retaining the underlying
monad's weakest-precondition interpretation. In particular, PCG64 and StdGen use the same
stateful interpretation when `RandomDo.WP.PseudoRandom` is imported.
-/

@[expose] public section

open MeasureTheory

namespace Std.WP

universe u v w w'

-- No separate core analogue: this forwards the interpretation through our sampling tag,
-- just as its monad and loop instances forward the underlying operations.
instance {tag : Type} {m : (α : Type u) → [MeasurableSpace α] → Type v}
    [MeasurableSpaceMonad m] [∀ α, [MeasurableSpace α] → MeasurableSpace (m α)]
    {Pred : Type w} {EPred : Type w'} [Assertion Pred] [MeasurableSpace Pred] [Assertion EPred]
    [WPMeasurableSpaceMonad m Pred EPred] :
    WPMeasurableSpaceMonad (WithSampling tag m) Pred EPred :=
  inferInstanceAs (WPMeasurableSpaceMonad m Pred EPred)

end Std.WP
