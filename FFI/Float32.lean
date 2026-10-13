/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

prelude
public import Init.Data.Float.Float32

@[expose] public section

namespace Float32

/-- `log (1 + x)`, the C99 `log1p`, accurate for small `x` where `log (1 + x)` loses the leading
digits of the result to the rounding of `1 + x`. -/
@[extern "log1pf"] opaque log1p (x : Float32) : Float32

end Float32
