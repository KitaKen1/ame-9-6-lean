import AME96.Phase
import AME96.Data
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

/-! Quadratic phase identities. The three initial lemmas adapt the Apache-2.0
GraphCharacter proof credited in the repository README. -/
namespace AME96
open scoped BigOperators

def quadratic {n p : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod p))
    (x : Fin n → ZMod p) : ZMod p :=
  ∑ i, ∑ j ∈ Finset.Ioi i, M i j * x i * x j

theorem quadratic_translate {n p : ℕ} (G : Fin n → Fin n → ZMod p)
    (x d : Fin n → ZMod p) :
    quadratic G (x + d) = quadratic G x + quadratic G d +
      ∑ i, ∑ j ∈ Finset.Ioi i,
        G i j * (x i * d j + d i * x j) := by
  have expand (i j : Fin n) :
      G i j * (x i + d i) * (x j + d j) =
        G i j * x i * x j + G i j * d i * d j +
          G i j * (x i * d j + d i * x j) := by ring
  simp only [quadratic, Pi.add_apply]
  simp_rw [expand, Finset.sum_add_distrib]

theorem upper_triangle_cross {n p : ℕ} (G : Fin n → Fin n → ZMod p)
    (hsym : ∀ i j, G i j = G j i) (hdiag : ∀ i, G i i = 0)
    (x d : Fin n → ZMod p) :
    (∑ i, ∑ j ∈ Finset.Ioi i,
      G i j * (x i * d j + d i * x j)) =
      ∑ i, x i * ∑ j, G i j * d j := by
  let term := fun i j : Fin n => x i * (G i j * d j)
  have hupper :
      (∑ i, ∑ j ∈ Finset.Ioi i,
        G i j * (x i * d j + d i * x j)) =
        ∑ i, ∑ j ∈ Finset.Ioi i, (term i j + term j i) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [term]
    rw [← hsym i j]
    ring
  rw [hupper, Finset.sum_sum_Ioi_add_eq_sum_sum_off_diag]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  change (∑ j ∈ ({i}ᶜ : Finset (Fin n)), term i j) = ∑ j, term i j
  have herase : Finset.univ.erase i = ({i}ᶜ : Finset (Fin n)) := by
    ext j
    simp [eq_comm]
  rw [← herase]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp [term, hdiag]

theorem quadratic_difference {n p : ℕ} (G : Fin n → Fin n → ZMod p)
    (hsym : ∀ i j, G i j = G j i) (hdiag : ∀ i, G i i = 0)
    (x y : Fin n → ZMod p) :
    quadratic G x - quadratic G y = quadratic G (x - y) +
      ∑ i, y i * ∑ j, G i j * (x j - y j) := by
  have hexpand := quadratic_translate G y (x - y)
  rw [show y + (x - y) = x by abel] at hexpand
  rw [hexpand, upper_triangle_cross G hsym hdiag]
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

end AME96
