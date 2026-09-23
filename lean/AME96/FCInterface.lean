import FormalConjectures.OpenQuantumProblems.«35»

/-! Exact target interface at FC commit 2a46c7bd74505b85f4967475bb733ded0ef8d348.
This is an implication with explicit hypotheses, not an AME existence proof. -/
namespace AME96
open OpenQuantumProblem35
open scoped BigOperators

theorem existsAME_of_reductions (ψ : StateVector 9 6)
    (hnorm : IsNormalized ψ)
    (hred : ∀ (π : Equiv.Perm (Fin 9)) (x y : Config 4 6),
      (∑ z : Config 5 6,
        (permuteState π ψ) (combineFirst 4 (by decide) x z) *
          star ((permuteState π ψ) (combineFirst 4 (by decide) y z))) =
            if x = y then (1296 : ℂ)⁻¹ else 0) :
    ExistsAME 9 6 := by
  refine ⟨ψ, hnorm, ?_⟩
  intro π
  unfold HasMaximallyMixedFirstReduction
  ext x y
  change (∑ z : Config 5 6,
    (permuteState π ψ) (combineFirst 4 (by decide) x z) *
      star ((permuteState π ψ) (combineFirst 4 (by decide) y z))) = _
  rw [hred, maximallyMixed_apply, card_config]
  norm_num

end AME96
