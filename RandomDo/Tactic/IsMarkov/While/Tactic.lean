/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import RandomDo.Tactic.IsMarkov.While.Termination

/-!
# A tactic for the termination of `while` loops

`terminates` proves the goal `Terminates f b` that `is_markov` hands back for a `while` loop, from
an invariant, a variant and a probability given on the states of the loop. It applies a rule of
`RandomDo.Tactic.IsMarkov.While.Termination`, unfolds the step of the loop on its successors, and
leaves the remaining conditions as goals about the states only.

## Main declarations

* `loop_step`: simplifies a goal about one step of a loop into conditions on its successors.
* `terminates`: proves the termination of a loop by one of the rules.
-/

public meta section

open Lean

/-- `loop_step [h₁, …]` simplifies a goal about one step of a loop: a property that almost every
successor of a state satisfies, the probability of a set of successors, or an arithmetic condition.
It evaluates the step on its successors, with the additional simp lemmas `h₁, …` for the
definitions of the program, splits on the conditions of the program, and tries to close the
resulting goals, which only mention the state. -/
syntax (name := loopStep) "loop_step" (" [" term,* "]")? : tactic

macro_rules
  | `(tactic| loop_step $[[$ls,*]]?) => do
    let ls : Array Term := (ls.map (·.getElems)).getD #[]
    `(tactic| (
      try intro $(mkIdent `s) $(mkIdent `hs)
      try simp only at *
      try simp only [MeasureTheory.ae_iff]
      try split_ifs
      all_goals try norm_num [MeasureTheory.Measure.dirac_apply, Set.indicator_apply,
        ENNReal.toReal_add, ENNReal.toReal_ofReal', ENNReal.mul_eq_top, $[$ls:term],*] at *
      -- A measure followed by a deterministic successor is its image, and the probability of a set
      -- under the image is at least the probability of its preimage.
      all_goals try rw [MeasureTheory.Measure.bind_dirac_eq_map]
      all_goals try refine le_trans ?_ (ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _)
        (MeasureTheory.Measure.le_map_apply ?_ _))
      all_goals try fun_prop
      all_goals try simp only [Set.preimage_ofPred_eq] at *
      all_goals try split_ifs
      all_goals try norm_num [ENNReal.toReal_add, ENNReal.toReal_ofReal', ENNReal.mul_eq_top] at *
      all_goals repeat' apply And.intro
      all_goals try first | done | trivial | assumption | omega | linarith | positivity))

/-- The invariant of `terminates`: the given property of the running states, whose stability is left
as the goal `step`, or the property that always holds. -/
def invariant (P? : Option Term) : MacroM Term :=
  match P? with
  | some P => `(({ running := $P, step := ?step } : MeasurableSpaceMonadWhile.LoopInvariant _))
  | none => `(({ running := fun _ ↦ True
                 step := fun _ _ ↦ Filter.Eventually.of_forall fun t ↦ by cases t <;> trivial } :
      MeasurableSpaceMonadWhile.LoopInvariant _))

/-- `terminates` proves the termination of a `while` loop, the goal `Terminates f b` that
`is_markov` hands back (after `intro` of the parameters the loop depends on).

* `terminates (prob := ε)` applies `Terminates.mcIverMorgan_immediateEscape`: every step stops with
  probability at least `ε > 0`.
* `terminates (variant := U) (bound := N) (prob := ε)` applies
  `Terminates.majumdarSathiyanarayana_variantRule`, with a variant `U : σ → ℕ` on the states, at
  most `N`, decreased with probability at least `ε > 0` by every step that does not stop. Stopping
  counts as decreasing `U`.
* `(invariant := P)`, before the other arguments, restricts both to the states satisfying
  `P : σ → Prop`, which almost every step keeps.
* `[h₁, …]`, after the other arguments, are simp lemmas for the definitions of the program.

The variant rule takes a variant `U'` on the states `ForInStep σ` of the transition system, with
`Lo ≤ U' < Hi`, and a probability `> ε` of decreasing it. `terminates` applies it to
`U' (done s) = 0` and `U' (yield s) = U s + 1`, between `Lo = 0` and `Hi = N + 2`, with `ε / 2`:
* A step from `yield s` that stops goes to some `done s'`, and counts as decreasing `U'` only if
  `U' (done s') < U' (yield s)`. As `U` can be `0` on a running state (when the loop is about to
  stop, as `countdown` at `0`), the terminal states need a value below all the values of `U`:
  hence the shift of `U` by `1` on the running states, the terminal states taking `0`. A step to
  `yield s'` still decreases `U'` exactly when it decreases `U`.
* On the invariant, `U s ≤ N`, so `0 ≤ U' ≤ N + 1`, and the strict upper bound of the rule is
  `N + 2`: one for the shift, one for passing from `≤` to `<`.
* `(prob := ε)` asks for a probability at least `ε`, while the rule asks for one greater than its
  constant: a probability `≥ ε` is `> ε / 2`.

The conditions it cannot prove are left as goals about the states only. -/
syntax (name := terminatesTac) "terminates" (atomic(" (" &"invariant") " := " term ")")?
  (atomic(" (" &"variant") " := " term ")")? (atomic(" (" &"bound") " := " term ")")?
  " (" &"prob" " := " term ")" (" [" term,* "]")? : tactic

macro_rules
  | `(tactic| terminates $[(invariant := $P?)]? (prob := $ε) $[[$ls,*]]?) => do
    let ls : Array Term := (ls.map (·.getElems)).getD #[]
    let I ← invariant P?
    `(tactic| (
      intros
      refine MeasurableSpaceMonadWhile.Terminates.mcIverMorgan_immediateEscape $I $ε ?pos
        ?init ?stop
      all_goals try loop_step [$[$ls:term],*]))
  | `(tactic| terminates $[(invariant := $P?)]? (variant := $U) (bound := $N) (prob := $ε)
      $[[$ls,*]]?) => do
    let ls : Array Term := (ls.map (·.getElems)).getD #[]
    let I ← invariant P?
    let P ← P?.getDM `(fun _ ↦ True)
    `(tactic| (
      intros
      -- `U` shifted by `1` on the running states, below which the terminal states are `0`: see the
      -- docstring for the bounds `0` and `N + 2` and for `ε / 2`.
      refine MeasurableSpaceMonadWhile.Terminates.majumdarSathiyanarayana_variantRule $I
        (fun t ↦ ForInStep.casesOn (motive := fun _ ↦ ℤ) t (fun _ ↦ 0) fun s ↦ (($U s : ℕ) : ℤ) + 1)
        0 ((($N : ℕ) : ℤ) + 2) ($ε / 2) (half_pos ?pos) ?init ?bounds
        (fun $(mkIdent `s) $(mkIdent `hs) ↦ (half_lt_self ?pos).trans_le ?progress) ?measurable
      -- The bound of the lifted variant, from the bound `U ≤ N` on the states of the invariant.
      case' bounds =>
        intro t $(mkIdent `hs)
        cases t with
        | done _ => dsimp only; omega
        | yield $(mkIdent `s) =>
          replace $(mkIdent `hs) : ($P) $(mkIdent `s) := $(mkIdent `hs)
          try dsimp only at $(mkIdent `hs):ident ⊢
          refine (fun h : ($U) $(mkIdent `s) ≤ ($N) ↦ by (try simp only [] at h); omega) ?_
          try loop_step [$[$ls:term],*]
      -- The measurability of the lifted variant, from the measurability of `U`.
      case' measurable => first
        | exact Measurable.of_discrete
        | (refine MeasurableSpaceMonadWhile.measurable_casesOn measurable_const
            (((Measurable.of_discrete (f := fun n : ℕ ↦ (n : ℤ))).comp ?_).add_const 1)
           first | fun_prop | measurability | skip)
      try case' step => try loop_step [$[$ls:term],*]
      try case' init => try loop_step [$[$ls:term],*]
      try case' pos => try loop_step [$[$ls:term],*]
      try case' progress => try loop_step [$[$ls:term],*]))
  | `(tactic| terminates $[(invariant := $_)]? (variant := $_) (prob := $_) $[[$_,*]]?) =>
    Macro.throwError "terminates: a variant needs a bound, given by `(bound := N)`"
  | `(tactic| terminates $[(invariant := $_)]? (bound := $_) (prob := $_) $[[$_,*]]?) =>
    Macro.throwError "terminates: a bound needs a variant, given by `(variant := U)`"

end
