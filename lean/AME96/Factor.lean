import AME96.FirstCut
import AME96.Phase

namespace AME96
open scoped BigOperators

/-- The environment product appearing in the paper's partial-trace formula.
Its derivation from the nine-party amplitude is proved in Reduction.lean. -/
noncomputable def environmentProduct (s : Selected) (o : Outside) (d e : Difference) : ℂ :=
  (∏ i : Fin 5, ∑ y : ZMod 3, ZMod.stdAddChar (alpha s o d e i * y)) *
  (∏ i : Fin 5, ∑ x : Fin 2, (-1 : ℂ) ^ ((binaryCoeff s o d i).val * x.val) *
    ZMod.stdAddChar (beta s o d e i * (x.val : ZMod 3)))

/-- The finite cancellation criterion implies a zero complex environment product. -/
theorem environmentProduct_zero (s : Selected) (o : Outside) (d e : Difference)
    (h : Cancels s o d e) : environmentProduct s o d e = 0 := by
  rcases h with ⟨i, hi⟩ | ⟨i, hr, hb⟩
  · have hz : (∏ j : Fin 5, ∑ y : ZMod 3,
        ZMod.stdAddChar (alpha s o d e j * y)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (ternary_cancel _ hi)
    simp only [environmentProduct, hz, zero_mul]
  · have hz : (∏ j : Fin 5, ∑ x : Fin 2,
        (-1 : ℂ) ^ ((binaryCoeff s o d j).val * x.val) *
          ZMod.stdAddChar (beta s o d e j * (x.val : ZMod 3))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (binary_cancel _ _ hr hb)
    simp only [environmentProduct, hz, mul_zero]

/-- The first-cut finite check implies this instance of the environment-product identity. -/
theorem firstCut_environmentProduct_zero (d e : Difference) (h : d ≠ 0 ∨ e ≠ 0) :
    environmentProduct firstSelected firstOutside d e = 0 :=
  environmentProduct_zero _ _ _ _ (firstCut_cancels d e h)

end AME96
