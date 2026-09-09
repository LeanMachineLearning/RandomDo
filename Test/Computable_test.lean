module

public import RandomDo
public meta import RandomDo

set_option linter.style.header false

open MeasureTheory ProbabilityTheory NumLean

universe v

variable {m : (α : Type) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]

/-! ## Une capacité dont le type de valeur est le même des deux côtés

Le crochet de la `MeasurableSpace` peut rester implicite dans le paramètre de la classe : Lean la
synthétise alors dans le type du champ, et `(by infer_instance)` devient inutile. -/

/-- Tirer un bit. -/
class HasBit (m : (α : Type) → [MeasurableSpace α] → Type v) where
  /-- Le tirage. -/
  bit : m Bool

noncomputable instance : HasBit Measure where
  bit := bernoulliMeasure true false ⟨(1 : ℝ) / 2, by norm_num⟩

/-- Un programme qui ne dit pas dans quelle monade il vit. -/
def sampleBitsArray [HasBit m] (n : ℕ) : m (Array Bool) := rdo
  let mut xs : Array Bool := #[]
  for _ in List.range n rdo
    let b ← HasBit.bit (m := m)
    xs := xs.push b
  return xs

/-! ## La même chose pour la gaussienne

`Bool` est le même objet dans les deux mondes, mais les réels ne le sont pas : une mesure vit sur
`ℝ`, un échantillonneur rend un `Float`. La classe laisse donc le type des scalaires libre, et c'est
chaque instance qui le fixe. -/

/-- Un espace mesurable sur `Float` : il est fini, donc toutes ses parties sont mesurables. -/
instance : MeasurableSpace Float := ⊤

/-- Tirer une gaussienne de moyenne et de variance données, à valeurs dans `R`. -/
class HasGaussian (m : (α : Type) → [MeasurableSpace α] → Type v)
    (R : Type) [MeasurableSpace R] where
  /-- Le tirage, de moyenne le premier argument et de variance le second. -/
  gaussian : R → R → m R

noncomputable instance : HasGaussian Measure ℝ where
  gaussian μ v := gaussianReal μ v.toNNReal

/-- La monade qui échantillonne, vue comme une `MeasurableSpaceMonad` comme les autres. -/
abbrev RandM := Monad.toMeasurableSpaceMonad (RandPCG IO)

instance : HasGaussian RandM Float where
  gaussian μ v := normal' μ v

/- Les scalaires sur lesquels un programme compte : de quoi écrire `0` et `+`. Les lois ne sont
pas demandées, seulement les opérations, ce qui laisse `Float` passer. -/
variable {R : Type} [MeasurableSpace R] [Add R] [OfNat R 0] [OfNat R 1]

/-- Un seul programme, écrit une fois. -/
def ex1 [HasGaussian m R] : m R := rdo
  let mut x : R := 0
  for _ in List.range 10 rdo
    let y ← HasGaussian.gaussian (m := m) 0 1
    x := x + y
  return x

/-- Lu comme une mesure. -/
noncomputable example : Measure ℝ := ex1

/- Lu comme un échantillonneur, et il tourne. -/
run_cmd do
  let x ← (IO.runRandPCGWith 42 (ex1 (m := RandM) (R := Float)) : IO Float)
  Lean.logInfo m!"ex1 échantillonné (seed 42) = {x}"
