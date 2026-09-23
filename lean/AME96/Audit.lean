import AME96

/-! Audit roots for the explicit FC existence proof. -/
#print axioms AME96.G_symmetric
#print axioms AME96.firstCut_cancels
#print axioms AME96.ternary_cancel
#print axioms AME96.binary_cancel
#print axioms AME96.character_mul_star
#print axioms AME96.firstCut_environmentProduct_zero
#print axioms AME96.state_normalized
#print axioms AME96.existsAME_of_reductions

#print axioms AME96.allCuts_cancels
#print axioms AME96.allCuts_complete
#print axioms AME96.allCuts_partition
#print axioms AME96.everyPartition_cancels
#print axioms AME96.mixedPhase_environment_sum
#print axioms AME96.reduction_eq
#print axioms AME96.state_isAME
#print axioms AME96.exists_ame_9_6
#print axioms AME96.ame_9_6_answer_true

/-- The original and constructed existence statements use exactly the same FC definition. -/
example : OpenQuantumProblem35.ExistsAME 9 6 := AME96.exists_ame_9_6
example : answer(True) ↔ OpenQuantumProblem35.ExistsAME 9 6 :=
  AME96.ame_9_6_answer_true

/-- The diagonal case is deliberately not classified as a cancellation. -/
example : ¬ AME96.Cancels AME96.firstSelected AME96.firstOutside 0 0 := by
  decide +kernel
