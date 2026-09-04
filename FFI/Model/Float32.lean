/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

prelude
public import Init.Data.Float.Model.Float32
public import FFI.FMA

-- This file is part of the logical model for floats which authors of float libraries
-- need to rely on.
@[expose] public section

namespace Float32.Model

open Float.Model (Format UnpackedFloat)

/--
Compute the fused multiply-add `a * b + c` of three `Float32.Model`, with a single rounding.
-/
def fma (a b c : Float32.Model) : Float32.Model :=
  pack (UnpackedFloat.fma Format.binary32 a.unpack b.unpack c.unpack)

end Float32.Model
