/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

prelude
public import Init.Data.Float.Float
public import FFI.Model.Float

@[expose] public section

namespace Float

/--
Computes the fused multiply-add `x * y + z` of three floating-point numbers. This operation is
performed with a single rounding, which can be more accurate than performing the multiplication and
addition separately.

This function has a logical model in terms of `Float.Model`. It is implemented in compiled code by
the C function `fma`.
-/
@[extern "fma"] def fma : Float → Float → Float → Float :=
  fun x y z => .ofModel (x.toModel.fma y.toModel z.toModel)

/-- `log (1 + x)`, the C99 `log1p`, accurate for small `x` where `log (1 + x)` loses the leading
digits of the result to the rounding of `1 + x`. -/
@[extern "log1p"] opaque log1p (x : Float) : Float

end Float
