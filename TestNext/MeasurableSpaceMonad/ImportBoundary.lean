/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

import RandomDoNext

/-!
# Isolation of the polymorphic foundation

The complete rebuilt library must not pull in the original monad classes, concrete measure
semantics, or random-number implementations. These checks also catch transitive imports.
-/

assert_not_exists MeasurableSpaceMonad MeasureTheory.Measure PseudoRandomM NumLean.RandPCG
