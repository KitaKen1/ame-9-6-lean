import AME96.Finite

namespace AME96

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
/-- All 3^8 - 1 nonzero difference types on the cut {0,1,2,3}. -/
theorem firstCut_cancels : ∀ d e : Difference,
    d ≠ 0 ∨ e ≠ 0 → Cancels firstSelected firstOutside d e := by
  decide +kernel

end AME96

#print axioms AME96.firstCut_cancels
