/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import RandomDoNext.MeasurableSpaceMonad.Core
public import RandomDoNext.MeasurableSpaceMonad.Notation

/-!
# Measurable-space monads

The polymorphic foundation of the rebuilt library. `Core` contains operations, laws, and
iteration interfaces; `Notation` contains their `rdo` elaborators. Concrete interpretations
and sampling implementations belong outside this subtree.

`RandomDoNext` is the staging module root. Declaration namespaces already use `RandomDo`, so
promoting the library will change module paths without renaming its mathematical API.
-/
