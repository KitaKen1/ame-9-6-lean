import AME96.CutData

namespace AME96
open Matrix
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Each listed pair is a disjoint, exhaustive partition of all nine parties. -/
theorem allCuts_partition : ∀ k : Fin 126, Function.Bijective
    (fun i : Fin 4 ⊕ Fin 5 => Sum.elim (cutSelected k) (cutOutside k) i) := by
  decide +kernel

/-- The table covers every four-element subset, not merely 126 chosen examples. -/
theorem allCuts_complete : ∀ S : Finset (Fin 9), S.card = 4 →
    ∃ k : Fin 126, Finset.univ.image (cutSelected k) = S := by
  decide +kernel


end AME96

#print axioms AME96.allCuts_complete
