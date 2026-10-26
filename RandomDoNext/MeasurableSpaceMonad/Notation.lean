/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDoNext.MeasurableSpaceMonad.Notation.Basic
public import RandomDoNext.MeasurableSpaceMonad.Notation.ForIn

/-!
# Syntax for polymorphic measurable-space monad programs

Provides `rdo` and collection iteration. The operations and iteration instances are supplied
by the caller; importing this module does not select a concrete interpretation.
-/
