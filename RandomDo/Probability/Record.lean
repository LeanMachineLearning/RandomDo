/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import RandomDo.Monad.Notation
public import RandomDo.Monad.Instances
public import RandomDo.Tactic.IsMarkov
public meta import Lean.Elab.Do

/-!
# Recording a value of an `rdo` program as a random variable

The trace of an `rdo` program (`RandomDo.Probability.Trace`) has one coordinate per `←`. Values the
program computes without drawing them — a `let mut` accumulator, an intermediate quantity — are
therefore *not* coordinates: they can be spoken about only through whatever the program did draw.

`record` is the annotation that changes that. Writing

```
record N
```

on a line of an `rdo` block turns `N` into a coordinate of the trace from that point on, hence into
a random variable one can state laws about and condition on. It denotes the one-point distribution
at `N`, so it never changes what the program computes (`record_bind`); all it does is put a `←` in
the program text where there was none, which is exactly what the trace is built from.

## Main definitions

* `RDo.record x`: the one-point distribution at `x`, marked so that the trace keeps a coordinate
  for it.
* the `record x, y, …` `doElem`, sugar for `x ← RDo.record x` on each of them.

## Main results

* `RDo.record_bind`, `RDo.record_bind_of_isMarkov`: drawing from `record x` and carrying on is the
  same as carrying on with `x`. Recording never changes the measure a program denotes; the second
  form is the one to feed `simp (disch := is_markov)` to erase every `record` from a program.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MeasurableSpacePure MeasurableSpaceBind

namespace RDo

universe u

variable {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]

/-- `record x` is the one-point distribution at `x`. Drawing from it changes nothing —
`record x = mPure x` — but the `←` it is drawn with gives the program's trace a coordinate holding
the value of `x` at that point, so that `x` becomes a random variable of the program.

Inside an `rdo` block, write `record x` (sugar for `x ← RDo.record x`). -/
noncomputable def record (x : α) : Measure α := Measure.dirac x

lemma record_eq_mPure (x : α) : record x = mPure x := rfl

instance (x : α) : IsProbabilityMeasure (record x) := by
  rw [record]; infer_instance

instance : IsMarkov (record : α → Measure α) :=
  ⟨Measure.measurable_dirac, fun _ ↦ inferInstance⟩

/-- **Recording is transparent.** Drawing `x` from `record x` and carrying on is the same as
carrying on with `x`: inserting a `record` never changes the measure an `rdo` program denotes. -/
@[simp]
lemma record_bind (x : α) {f : α → Measure β} (hf : Measurable f) : record x >>=ₘ f = f x :=
  Measure.dirac_bind hf x

/-- `record_bind` in the shape a `simp` call can use with `is_markov` as its discharger:
`simp (disch := is_markov) only [record_bind_of_isMarkov]` erases every `record` from a program. -/
lemma record_bind_of_isMarkov (x : α) (f : α → Measure β) (h : IsMarkov f) :
    record x >>=ₘ f = f x :=
  Measure.dirac_bind h.measurable x

end RDo

end

public meta section

open Lean Lean.Parser Lean.Parser.Term Lean.Elab Lean.Elab.Do

namespace RDo

/-- `record x, y, …` inside an `rdo` block records the variables `x`, `y`, … as random variables of
the program at that point: each becomes a coordinate of the program's trace, so that laws and
conditional laws can be stated about it. It is sugar for `x ← RDo.record x`, and changes nothing
about what the program computes — see `RDo.record_bind`.

The variables must be `let mut` variables, since each is reassigned from its own recording. To
record an arbitrary expression, write `let y ← RDo.record e` instead.

Note that this declaration reserves `record` as a token, so `RDo.record` has to be written
qualified (or escaped as `«record»`) once this module is imported. -/
syntax (name := rdoRecord) "record " Lean.Parser.ident,+ : doElem

/-- Expand `record x, y` into one reassignment per variable. -/
@[macro rdoRecord] def expandRdoRecord : Macro := fun stx => do
  let `(doElem| record $xs:ident,*) := stx | Macro.throwUnsupported
  let items ← xs.getElems.mapM fun x => `(doSeqItem| $x:ident ← RDo.record $x)
  `(doElem| do $items*)

end RDo

end
