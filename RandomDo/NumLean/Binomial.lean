/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import RandomDo.NumLean.PCG64

/-!
# The binomial distribution

`binomial n p` draws exactly what numpy's `Generator.binomial` draws: the inversion of the
cumulative distribution where the mean `n * p` is at most `30`, the BTPE algorithm of
Kachitvichyanukul and Schmeiser beyond, and the mirror image of either when `p > 1 / 2`.

`binomial`, which chooses between the two and mirrors them, is in
`RandomDo.NumLean.Distributions`, with the other distributions.

## Main definitions

* `Inversion`, `inversionSetup`, `inversionDraw`: numpy's `random_binomial_inversion`.
* `Btpe`, `btpeSetup`, `Btpe.accept`, `btpeDraw`: numpy's `random_binomial_btpe`.

## References

* V. Kachitvichyanukul and B. W. Schmeiser, *Binomial random variate generation*, Communications
  of the ACM 31 (1988), 216-222.
* numpy's `numpy/random/src/distributions/distributions.c`.
-/

@[expose] public section

namespace NumLean

/-! ## Inversion -/

/-- The constants the inversion reads a draw against. -/
structure Inversion where
  /-- The number of trials. -/
  n : Float
  /-- The probability of a success, at most one half. -/
  p : Float
  /-- The probability of a failure, `1 - p`. -/
  q : Float
  /-- `q ^ n`, the probability that no trial succeeds. -/
  qn : Float
  /-- The number of successes past which the walk gives up and starts over. -/
  bound : Float

/-- The constants of `random_binomial_inversion`, for `p ≤ 0.5` and `n * p ≤ 30`. -/
@[inline] def inversionSetup (n p : Float) : Inversion :=
  let q := 1.0 - p
  let np := n * p
  let b := np + 10.0 * Float.sqrt (np * q + 1)
  { n, p, q, qn := Float.exp (n * Float.log q), bound := if n < b then n else b }

/-- Walk up the cumulative distribution from zero until it passes `u`, as the loop of
`random_binomial_inversion`. Answers `-1` where the walk runs past `bound`, which the tail beyond
it is too thin to reach and where numpy starts the draw over. -/
partial def inversionWalk (s : Inversion) (x px u : Float) : Float :=
  if u > px then
    let x := x + 1
    if x > s.bound then -1
    else inversionWalk s x (((s.n - x + 1) * s.p * px) / (x * s.q)) (u - px)
  else x

/-- Sample by inverting the cumulative distribution, as numpy's `random_binomial_inversion`. -/
partial def inversionDraw (s : Inversion) : RandPCG IO Float := do
  let x := inversionWalk s 0 s.qn (← random)
  if x < 0 then inversionDraw s else return x

/-! ## BTPE -/

/-- The constants BTPE reads a draw against. -/
structure Btpe where
  /-- The number of trials. -/
  n : Float
  /-- The probability of a success, at most one half. -/
  r : Float
  /-- The probability of a failure, `1 - r`. -/
  q : Float
  /-- The mode of the distribution. -/
  m : Float
  /-- The middle of the triangle, `m + 1 / 2`. -/
  xm : Float
  /-- The half-width of the triangle. -/
  p1 : Float
  /-- The left end of the parallelogram. -/
  xl : Float
  /-- The right end of the parallelogram. -/
  xr : Float
  /-- The height of the parallelogram, relative to the triangle. -/
  c : Float
  /-- The rate of the left exponential tail. -/
  laml : Float
  /-- The rate of the right exponential tail. -/
  lamr : Float
  /-- The area of the triangle and the parallelogram. -/
  p2 : Float
  /-- The area of the triangle, the parallelogram and the left tail. -/
  p3 : Float
  /-- The area of all four regions, which a draw is scaled by. -/
  p4 : Float
  /-- The variance `n * r * q`. -/
  nrq : Float

/-- The constants of `random_binomial_btpe`, for `p ≤ 0.5` and `n * p > 30`. -/
@[inline] def btpeSetup (n p : Float) : Btpe :=
  let r := if p < 1.0 - p then p else 1.0 - p
  let q := 1.0 - r
  let fm := n * r + r
  let m := Float.floor fm
  let p1 := Float.floor (2.195 * Float.sqrt (n * r * q) - 4.6 * q) + 0.5
  let xm := m + 0.5
  let xl := xm - p1
  let xr := xm + p1
  let c := 0.134 + 20.5 / (15.3 + m)
  let al := (fm - xl) / (fm - xl * r)
  let ar := (xr - fm) / (xr * q)
  let laml := al * (1.0 + al / 2.0)
  let lamr := ar * (1.0 + ar / 2.0)
  let p2 := p1 * (1.0 + 2.0 * c)
  let p3 := p2 + c / laml
  { n, r, q, m, xm, p1, xl, xr, c, laml, lamr, p2, p3, p4 := p3 + c / lamr, nrq := n * r * q }

/-- One term of the Stirling series bounding `log` of a factorial, as the last test of BTPE spells
it out. `u2` is `u * u`. -/
@[inline] def btpeStirling (u u2 : Float) : Float :=
  (13680.0 - (462.0 - (132.0 - (99.0 - 140.0 / u2) / u2) / u2) / u2) / u / 166320.0

/-- The ratios of the probabilities from the mode up to `y`, multiplied into `f` one at a time as
the step 50 of `random_binomial_btpe` takes them. -/
partial def btpeUp (a s f i y : Float) : Float :=
  if i ≤ y then btpeUp a s (f * (a / i - s)) (i + 1) y else f

/-- The ratios from `y` up to the mode, divided out of `f` one at a time. Dividing the running
value and dividing by the product do not round alike, and BTPE reads the first. -/
partial def btpeDown (a s f i m : Float) : Float :=
  if i ≤ m then btpeDown a s (f / (a / i - s)) (i + 1) m else f

/-- Whether BTPE accepts the candidate `y` drawn with `v`, as the steps 50 and 52 of
`random_binomial_btpe`: by the explicit product of the ratios of the probabilities between the mode
and `y` when the two are close, and by a squeeze then the Stirling bound otherwise. -/
def Btpe.accept (b : Btpe) (y v : Float) : Bool := Id.run do
  let k := Float.abs (y - b.m)
  unless k > 20 && k < b.nrq / 2.0 - 1 do
    let s := b.r / b.q
    let a := s * (b.n + 1)
    if b.m < y then return !(v > btpeUp a s 1.0 (b.m + 1) y)
    if b.m > y then return !(v > btpeDown a s 1.0 (y + 1) b.m)
    return !(v > 1.0)
  let rho := (k / b.nrq) * ((k * (k / 3.0 + 0.625) + 0.16666666666666666) / b.nrq + 0.5)
  let t := -k * k / (2 * b.nrq)
  let a := Float.log v
  if a < t - rho then return true
  if a > t + rho then return false
  let x1 := y + 1
  let f1 := b.m + 1
  let z := b.n + 1 - b.m
  let w := b.n - y + 1
  return !(a > b.xm * Float.log (f1 / x1) + (b.n - b.m + 0.5) * Float.log (z / w)
    + (y - b.m) * Float.log (w * b.r / (x1 * b.q))
    + btpeStirling f1 (f1 * f1) + btpeStirling z (z * z)
    + btpeStirling x1 (x1 * x1) + btpeStirling w (w * w))

/-- Draw a candidate from the triangle, the parallelogram or one of the two exponential tails, and
start over until one is accepted, as the steps 10 to 60 of `random_binomial_btpe`. -/
partial def btpeDraw (b : Btpe) : RandPCG IO Float := do
  let u := (← random) * b.p4
  let v ← random
  if u ≤ b.p1 then
    return Float.floor (b.xm - b.p1 * v + u)
  else if u ≤ b.p2 then
    let x := b.xl + (u - b.p1) / b.c
    let v := v * b.c + 1.0 - Float.abs (b.m - x + 0.5) / b.p1
    if v > 1.0 then btpeDraw b else
      let y := Float.floor x
      if b.accept y v then return y else btpeDraw b
  else if u ≤ b.p3 then
    let y := Float.floor (b.xl + Float.log v / b.laml)
    -- `v` can be zero, and the floor of the resulting infinity is no candidate.
    if y < 0 || v == 0.0 then btpeDraw b else
      let v := v * (u - b.p2) * b.laml
      if b.accept y v then return y else btpeDraw b
  else
    let y := Float.floor (b.xr - Float.log v / b.lamr)
    if y > b.n || v == 0.0 then btpeDraw b else
      let v := v * (u - b.p3) * b.lamr
      if b.accept y v then return y else btpeDraw b

end NumLean

end
