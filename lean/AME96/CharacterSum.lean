import AME96.Phase

/-! Finite character sums needed to evaluate the actual environment sum. -/
namespace AME96
open scoped BigOperators

theorem character_sum {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι]
    (f : ι → ZMod q) : ZMod.stdAddChar (∑ i, f i) = ∏ i, ZMod.stdAddChar (f i) := by
  classical
  have h (s : Finset ι) : ZMod.stdAddChar (∑ i ∈ s, f i) =
      ∏ i ∈ s, ZMod.stdAddChar (f i) := by
    induction s using Finset.induction with
    | empty => simp
    | @insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi,
        AddChar.map_add_eq_mul, ih]
  exact h Finset.univ

theorem binary_character_one : ZMod.stdAddChar (1 : ZMod 2) = (-1 : ℂ) := by
  have h : (∑ x : ZMod 2, ZMod.stdAddChar x) = 0 := by
    simpa using (AddChar.sum_eq_zero_of_ne_one
      (ZMod.isPrimitive_stdAddChar 2 (one_ne_zero : (1 : ZMod 2) ≠ 0)))
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide +kernel
  rw [huniv] at h
  simp at h
  linear_combination h

private theorem bit_cases : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide +kernel

theorem binary_character (r : ZMod 2) : ZMod.stdAddChar r = (-1 : ℂ) ^ r.val := by
  rcases bit_cases r with rfl | rfl <;> norm_num [binary_character_one, show (1 : ZMod 2).val = 1 from rfl]

theorem binary_character_mul (r x : ZMod 2) :
    ZMod.stdAddChar (r * x) = (-1 : ℂ) ^ (r.val * x.val) := by
  rcases bit_cases r with rfl | rfl <;>
    rcases bit_cases x with rfl | rfl <;> norm_num [binary_character_one, show (1 : ZMod 2).val = 1 from rfl]

end AME96
