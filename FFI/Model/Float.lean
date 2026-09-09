/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

prelude
public import Init.Data.Float.Model.Float
public import FFI.FMA

-- This file is part of the logical model for floats which authors of float libraries
-- need to rely on.
@[expose] public section

namespace Float.Model

/--
Compute the fused multiply-add `a * b + c` of three `Float.Model`, with a single rounding.
-/
def fma (a b c : Float.Model) : Float.Model :=
  pack (UnpackedFloat.fma Format.binary64 a.unpack b.unpack c.unpack)

end Float.Model
