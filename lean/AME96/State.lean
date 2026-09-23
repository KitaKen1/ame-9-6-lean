import AME96.Polynomial
import AME96.Phase
import AME96.FCInterface

/-! The supplied AME(9,6) candidate as a normalized state in the exact FC interface. -/
namespace AME96
open OpenQuantumProblem35
open scoped BigOperators

def localSixEquiv : Fin 2 × Fin 3 ≃ Fin 6 := finProdFinEquiv

theorem localSixEquiv_val (x : Fin 2) (y : Fin 3) :
    (localSixEquiv (x, y)).val = 3 * x.val + y.val := by
  change y.val + 3 * x.val = 3 * x.val + y.val
  omega

def bits (z : Config 9 6) (i : Fin 9) : ZMod 2 :=
  ((localSixEquiv.symm (z i)).1.val : ZMod 2)

def trits (z : Config 9 6) (i : Fin 9) : ZMod 3 :=
  ((localSixEquiv.symm (z i)).2.val : ZMod 3)

def liftedBits (z : Config 9 6) (i : Fin 9) : ZMod 3 :=
  ((localSixEquiv.symm (z i)).1.val : ZMod 3)

def ternaryPhase (z : Config 9 6) : ZMod 3 :=
  quadratic C (trits z) +
    (∑ i, ∑ j, liftedBits z i * B i j * trits z j) +
    quadratic H (liftedBits z)

noncomputable def coefficient : ℂ := (Real.sqrt ((6 : ℝ) ^ 9))⁻¹

/-- The supplied full-support phase state, with local label 3x+y. -/
noncomputable def amplitude (z : Config 9 6) : ℂ :=
  coefficient * ZMod.stdAddChar (quadratic G (bits z)) *
    ZMod.stdAddChar (ternaryPhase z)

noncomputable def state : StateVector 9 6 := mkStateVector amplitude

theorem amplitude_norm_sq (z : Config 9 6) : ‖amplitude z‖ ^ 2 = ((6 : ℝ) ^ 9)⁻¹ := by
  simp only [amplitude, norm_mul, character_norm, mul_one]
  simp only [coefficient, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow]
  rw [Real.sq_sqrt (by positivity)]

/-- Normalization of the actual FC state; this does not yet prove its AME property. -/
theorem state_normalized : IsNormalized state := by
  apply (isNormalized_iff_norm_sq_eq_one state).mpr
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ z : Config 9 6, ‖amplitude z‖ ^ 2) = 1
  simp only [amplitude_norm_sq, Finset.sum_const, Finset.card_univ,
    card_config, nsmul_eq_mul]
  norm_num

end AME96
