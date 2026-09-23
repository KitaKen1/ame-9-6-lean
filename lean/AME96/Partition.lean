import AME96.Polynomial

/-! Coordinate-free cuts and the cancellation of environment-only phase terms. -/
namespace AME96
open scoped BigOperators
abbrev Partition := (Fin 4 ⊕ Fin 5) ≃ Fin 9

def paste {R : Type*} (p : Partition) (a : Fin 4 → R) (u : Fin 5 → R) : Fin 9 → R :=
  fun i => Sum.elim a u (p.symm i)

@[simp] theorem paste_left {R : Type*} (p : Partition)
    (a : Fin 4 → R) (u : Fin 5 → R) (i : Fin 4) :
    paste p a u (p (.inl i)) = a i := by simp [paste]

@[simp] theorem paste_right {R : Type*} (p : Partition)
    (a : Fin 4 → R) (u : Fin 5 → R) (i : Fin 5) :
    paste p a u (p (.inr i)) = u i := by simp [paste]

theorem sum_partition {R : Type*} [AddCommMonoid R] (p : Partition) (f : Fin 9 → R) :
    (∑ i, f i) = (∑ j : Fin 4, f (p (.inl j))) + ∑ i : Fin 5, f (p (.inr i)) := by
  rw [← p.sum_comp f, Fintype.sum_sum_type]

theorem paste_sub {R : Type*} [Sub R] (p : Partition)
    (a b : Fin 4 → R) (u v : Fin 5 → R) :
    paste p a u - paste p b v = paste p (a - b) (u - v) := by
  funext i
  obtain ⟨i, rfl⟩ := p.surjective i
  cases i <;> simp

theorem paste_same_sub {R : Type*} [AddGroup R] (p : Partition)
    (a b : Fin 4 → R) (u : Fin 5 → R) :
    paste p a u - paste p b u = paste p (a - b) 0 := by
  rw [paste_sub, sub_self]

theorem sum_mul_paste_zero {R : Type*} [Semiring R] (p : Partition)
    (f : Fin 9 → R) (d : Fin 4 → R) :
    (∑ i, f i * paste p d 0 i) = ∑ j : Fin 4, f (p (.inl j)) * d j := by
  rw [sum_partition p]
  simp

/-- The environment enters a quadratic phase difference only linearly. -/
theorem quadratic_paste_difference {q : ℕ} (M : Matrix (Fin 9) (Fin 9) (ZMod q))
    (hsym : ∀ i j, M i j = M j i) (hdiag : ∀ i, M i i = 0)
    (p : Partition) (a b : Fin 4 → ZMod q) (u : Fin 5 → ZMod q) :
    quadratic M (paste p a u) - quadratic M (paste p b u) =
      (quadratic M (paste p a 0) - quadratic M (paste p b 0)) +
        ∑ i : Fin 5, u i * ∑ j : Fin 4, M (p (.inr i)) (p (.inl j)) * (a j - b j) := by
  have hform (v : Fin 5 → ZMod q) :
      quadratic M (paste p a v) - quadratic M (paste p b v) =
        quadratic M (paste p (a - b) 0) +
          (∑ i : Fin 4, b i * ∑ j : Fin 4,
            M (p (.inl i)) (p (.inl j)) * (a j - b j)) +
          ∑ i : Fin 5, v i * ∑ j : Fin 4,
            M (p (.inr i)) (p (.inl j)) * (a j - b j) := by
    rw [quadratic_difference M hsym hdiag, paste_same_sub]
    have hd (j : Fin 9) : paste p a v j - paste p b v j =
        paste p (a - b) 0 j := congrFun (paste_same_sub p a b v) j
    simp_rw [hd, sum_mul_paste_zero]
    rw [sum_partition p]
    simp only [paste_left, paste_right, Pi.sub_apply]
    abel
  rw [hform u, hform 0]
  simp

def bilinear {q : ℕ} (M : Matrix (Fin 9) (Fin 9) (ZMod q))
    (x y : Fin 9 → ZMod q) : ZMod q := ∑ i, ∑ j, x i * M i j * y j

/-- Expanding a bilinear form along a partition separates its four blocks. -/
theorem bilinear_paste {q : ℕ} (M : Matrix (Fin 9) (Fin 9) (ZMod q))
    (p : Partition) (a b : Fin 4 → ZMod q) (u v : Fin 5 → ZMod q) :
    bilinear M (paste p a u) (paste p b v) =
      (∑ i : Fin 4, ∑ j : Fin 4, a i * M (p (.inl i)) (p (.inl j)) * b j) +
      (∑ i : Fin 4, ∑ j : Fin 5, a i * M (p (.inl i)) (p (.inr j)) * v j) +
      (∑ i : Fin 5, ∑ j : Fin 4, u i * M (p (.inr i)) (p (.inl j)) * b j) +
      (∑ i : Fin 5, ∑ j : Fin 5, u i * M (p (.inr i)) (p (.inr j)) * v j) := by
  simp only [bilinear, sum_partition p, paste_left, paste_right, Finset.sum_add_distrib]
  abel

/-- The two differently oriented mixed crossing terms both survive. -/
theorem bilinear_paste_difference {q : ℕ} (M : Matrix (Fin 9) (Fin 9) (ZMod q))
    (p : Partition) (a a' b b' : Fin 4 → ZMod q) (u v : Fin 5 → ZMod q) :
    bilinear M (paste p a u) (paste p b v) -
      bilinear M (paste p a' u) (paste p b' v) =
      (bilinear M (paste p a 0) (paste p b 0) -
        bilinear M (paste p a' 0) (paste p b' 0)) +
      (∑ i : Fin 5, v i * ∑ j : Fin 4, M (p (.inl j)) (p (.inr i)) * (a j - a' j)) +
      (∑ i : Fin 5, u i * ∑ j : Fin 4, M (p (.inr i)) (p (.inl j)) * (b j - b' j)) := by
  simp only [bilinear_paste, Pi.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero,
    add_zero]
  have hc : (∑ i : Fin 4, ∑ j : Fin 5, a i * M (p (.inl i)) (p (.inr j)) * v j) -
      (∑ i : Fin 4, ∑ j : Fin 5, a' i * M (p (.inl i)) (p (.inr j)) * v j) =
      ∑ i : Fin 5, v i * ∑ j : Fin 4, M (p (.inl j)) (p (.inr i)) * (a j - a' j) := by
    rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => a' i * M (p (.inl i)) (p (.inr j)) * v j)]
    simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hd : (∑ i : Fin 5, ∑ j : Fin 4, u i * M (p (.inr i)) (p (.inl j)) * b j) -
      (∑ i : Fin 5, ∑ j : Fin 4, u i * M (p (.inr i)) (p (.inl j)) * b' j) =
      ∑ i : Fin 5, u i * ∑ j : Fin 4, M (p (.inr i)) (p (.inl j)) * (b j - b' j) := by
    simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  linear_combination hc + hd

end AME96
