import AME96.FastChecks
import AME96.CutMatrices
import AME96.CutCoverage

/-! All finite obligations are kernel-checked; the general certificate lemma
then covers every nonzero binary–ternary difference pair on every cut. -/
namespace AME96
open Matrix

theorem allCuts_cancels (k : Fin 126) (d e : Difference)
    (h : d ≠ 0 ∨ e ≠ 0) : Cancels (cutSelected k) (cutOutside k) d e :=
  cancels_of_small_certificate _ _ _ _ (cutLeftInverse_valid k)
    (cutCompatible_valid k) (fastCompatible_cancels k) d e h

end AME96

#print axioms AME96.allCuts_cancels
