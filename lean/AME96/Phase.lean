import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic

/-! Exact one-coordinate phase sums for the mixed binary–ternary construction. -/
namespace AME96
open scoped BigOperators

/-- A nontrivial ternary additive character sums to zero. -/
theorem ternary_sum (a : ZMod 3) :
    (∑ y : ZMod 3, ZMod.stdAddChar (a * y)) =
      if a = 0 then (3 : ℂ) else 0 := by
  by_cases ha : a = 0
  · simp [ha, ZMod.card]
  · simpa [ha] using
      (AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar 3 ha))

theorem ternary_cancel (a : ZMod 3) (ha : a ≠ 0) :
    (∑ y : ZMod 3, ZMod.stdAddChar (a * y)) = 0 := by
  simp [ternary_sum, ha]

/-- The binary sum may also carry a ternary phase. -/
theorem binary_sum (r : ZMod 2) (b : ZMod 3) :
    (∑ x : Fin 2, (-1 : ℂ) ^ (r.val * x.val) *
      ZMod.stdAddChar (b * (x.val : ZMod 3))) =
      1 + (-1 : ℂ) ^ r.val * ZMod.stdAddChar b := by
  simp [Fin.sum_univ_succ]

theorem binary_cancel (r : ZMod 2) (b : ZMod 3)
    (hr : r = 1) (hb : b = 0) :
    (∑ x : Fin 2, (-1 : ℂ) ^ (r.val * x.val) *
      ZMod.stdAddChar (b * (x.val : ZMod 3))) = 0 := by
  rw [binary_sum, hr, hb]
  change 1 + (-1 : ℂ) ^ 1 * ZMod.stdAddChar (0 : ZMod 3) = 0
  norm_num

theorem character_mul_star {N : ℕ} [NeZero N] (a b : ZMod N) :
    ZMod.stdAddChar a * star (ZMod.stdAddChar b) =
      ZMod.stdAddChar (a - b) := by
  change ZMod.stdAddChar a * (starRingEnd ℂ) (ZMod.stdAddChar b) = _
  rw [← AddChar.map_neg_eq_conj]
  simpa [sub_eq_add_neg] using
    (AddChar.map_add_eq_mul ZMod.stdAddChar a (-b)).symm

theorem character_norm {N : ℕ} [NeZero N] (a : ZMod N) :
    ‖ZMod.stdAddChar a‖ = 1 := by
  change ‖(↑(ZMod.toCircle a) : ℂ)‖ = 1
  exact Circle.norm_coe _

end AME96
