import AME96.Data

/-! Exact finite coefficients for the mixed binary–ternary cancellation criterion. -/
namespace AME96
open scoped BigOperators

abbrev Difference := Fin 4 → ZMod 3
abbrev Selected := Fin 4 → Fin 9
abbrev Outside := Fin 5 → Fin 9

def alpha (s : Selected) (o : Outside) (d e : Difference) (i : Fin 5) : ZMod 3 :=
  ∑ j, (C (o i) (s j) * e j + B (s j) (o i) * d j)

def binaryCoeff (s : Selected) (o : Outside) (d : Difference) (i : Fin 5) : ZMod 2 :=
  ∑ j, G (o i) (s j) * (if d j = 0 then 0 else 1)

def beta (s : Selected) (o : Outside) (d e : Difference) (i : Fin 5) : ZMod 3 :=
  ∑ j, (B (o i) (s j) * e j + H (o i) (s j) * d j)

/-- Exact sufficient condition for an off-diagonal entry to vanish. -/
def Cancels (s : Selected) (o : Outside) (d e : Difference) : Prop :=
  (∃ i, alpha s o d e i ≠ 0) ∨
  (∃ i, binaryCoeff s o d i = 1 ∧ beta s o d e i = 0)

instance (s : Selected) (o : Outside) (d e : Difference) :
    Decidable (Cancels s o d e) := by
  unfold Cancels
  infer_instance

def firstSelected : Selected := ![0, 1, 2, 3]
def firstOutside : Outside := ![4, 5, 6, 7, 8]

end AME96
