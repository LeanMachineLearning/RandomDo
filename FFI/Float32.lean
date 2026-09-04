/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

prelude
public import Init.Data.Float.Float32
public import FFI.Model.Float32

@[expose] public section

namespace Float32

/--
Computes the fused multiply-add `x * y + z` of three floating-point numbers. This operation is performed with a single rounding, which can be more accurate than performing the multiplication and addition separately.

This function has a logical model in terms of `Float32.Model`. It is implemented in compiled code
by the C function `fmaf`.
-/
@[extern "fmaf"] def fma : Float32 → Float32 → Float32 → Float32 :=
  fun x y z => .ofModel (x.toModel.fma y.toModel z.toModel)

/-- `log (1 + x)`, the C99 `log1p`, accurate for small `x` where `log (1 + x)` loses the leading
digits of the result to the rounding of `1 + x`. -/
@[extern "log1pf"] opaque log1p (x : Float32) : Float32

end Float32
