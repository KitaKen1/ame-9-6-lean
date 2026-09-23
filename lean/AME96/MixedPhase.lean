import AME96.Partition
import AME96.Finite

/-! Exact phase differences for the supplied mixed binary–ternary state. -/
namespace AME96
open scoped BigOperators

def liftBit (x : ZMod 2) : ZMod 3 := x.val

def liftBits {n : ℕ} (x : Fin n → ZMod 2) : Fin n → ZMod 3 := fun i => liftBit (x i)

@[simp] theorem liftBit_zero : liftBit 0 = 0 := rfl

@[simp] theorem liftBits_paste (p : Partition) (x : Fin 4 → ZMod 2) (u : Fin 5 → ZMod 2) :
    liftBits (paste p x u) = paste p (liftBits x) (liftBits u) := by
  funext i
  obtain ⟨i, rfl⟩ := p.surjective i
  cases i <;> simp [liftBits]

/-- A signed difference modulo 3 records exactly whether two bits differ. -/
theorem bit_sub_eq_indicator : ∀ x x' : ZMod 2,
    x - x' = if liftBit x - liftBit x' = 0 then 0 else 1 := by decide +kernel

def ternaryPolynomial (x y : Fin 9 → ZMod 3) : ZMod 3 :=
  quadratic C y + bilinear B x y + quadratic H x

noncomputable def mixedPhase (x : Fin 9 → ZMod 2) (y : Fin 9 → ZMod 3) : ℂ :=
  ZMod.stdAddChar (quadratic G x) * ZMod.stdAddChar (ternaryPolynomial (liftBits x) y)

def select (p : Partition) : Selected := fun j => p (.inl j)
def outside (p : Partition) : Outside := fun i => p (.inr i)

theorem binary_paste_difference (p : Partition) (x x' : Fin 4 → ZMod 2)
    (u : Fin 5 → ZMod 2) :
    quadratic G (paste p x u) - quadratic G (paste p x' u) =
      (quadratic G (paste p x 0) - quadratic G (paste p x' 0)) +
      ∑ i, binaryCoeff (select p) (outside p) (liftBits x - liftBits x') i * u i := by
  rw [quadratic_paste_difference G G_symmetric G_diagonal]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [binaryCoeff, select, outside, Pi.sub_apply, liftBits, bit_sub_eq_indicator]
  rw [mul_comm]
  rfl

theorem ternary_paste_difference (p : Partition)
    (x x' y y' : Fin 4 → ZMod 3) (u v : Fin 5 → ZMod 3) :
    ternaryPolynomial (paste p x u) (paste p y v) -
      ternaryPolynomial (paste p x' u) (paste p y' v) =
      (ternaryPolynomial (paste p x 0) (paste p y 0) -
        ternaryPolynomial (paste p x' 0) (paste p y' 0)) +
      (∑ i, alpha (select p) (outside p) (x - x') (y - y') i * v i) +
      (∑ i, beta (select p) (outside p) (x - x') (y - y') i * u i) := by
  have hC := quadratic_paste_difference C C_symmetric C_diagonal p y y' v
  have hH := quadratic_paste_difference H H_symmetric H_diagonal p x x' u
  have hB := bilinear_paste_difference B p x x' y y' u v
  simp only [ternaryPolynomial]
  simp only [alpha, beta, select, outside, Pi.sub_apply, Finset.sum_add_distrib,
    add_mul, Finset.sum_mul, Finset.mul_sum] at *
  simp only [mul_comm] at *
  linear_combination hC + hB + hH

/-- Before summing over environments, each amplitude product splits into local phases. -/
theorem mixedPhase_paste_mul_star (p : Partition)
    (x x' : Fin 4 → ZMod 2) (y y' : Fin 4 → ZMod 3)
    (u : Fin 5 → ZMod 2) (v : Fin 5 → ZMod 3) :
    mixedPhase (paste p x u) (paste p y v) *
      star (mixedPhase (paste p x' u) (paste p y' v)) =
      (mixedPhase (paste p x 0) (paste p y 0) *
        star (mixedPhase (paste p x' 0) (paste p y' 0))) *
      ZMod.stdAddChar (∑ i, alpha (select p) (outside p)
        (liftBits x - liftBits x') (y - y') i * v i) *
      (ZMod.stdAddChar (∑ i, binaryCoeff (select p) (outside p)
          (liftBits x - liftBits x') i * u i) *
        ZMod.stdAddChar (∑ i, beta (select p) (outside p)
          (liftBits x - liftBits x') (y - y') i * liftBit (u i))) := by
  have regroup (a b c d : ℂ) : a * b * star (c * d) =
      (a * star c) * (b * star d) := by simp only [star_mul]; ring
  simp only [mixedPhase, regroup, character_mul_star, liftBits_paste]
  rw [binary_paste_difference, ternary_paste_difference]
  have hzero : liftBits (0 : Fin 5 → ZMod 2) = 0 := by ext i; rfl
  simp only [hzero, AddChar.map_add_eq_mul, liftBits]
  ring

end AME96
