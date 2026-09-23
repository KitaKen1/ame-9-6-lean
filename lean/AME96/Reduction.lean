import AME96.State
import AME96.MixedPhase
import AME96.CharacterSum
import AME96.Factor

/-! Evaluate the environment sum of the defining phase state, without assumptions
about a precomputed amplitude table. -/
namespace AME96
open scoped BigOperators

/-- The exact product formula for all cuts and all pairs of inside labels. -/
theorem mixedPhase_environment_sum (p : Partition)
    (x x' : Fin 4 → ZMod 2) (y y' : Fin 4 → ZMod 3) :
    (∑ v : Fin 5 → ZMod 3, ∑ u : Fin 5 → ZMod 2,
      mixedPhase (paste p x u) (paste p y v) *
        star (mixedPhase (paste p x' u) (paste p y' v))) =
      (mixedPhase (paste p x 0) (paste p y 0) *
        star (mixedPhase (paste p x' 0) (paste p y' 0))) *
      environmentProduct (select p) (outside p) (liftBits x - liftBits x') (y - y') := by
  conv_lhs =>
    arg 2
    ext v
    arg 2
    ext u
    rw [mixedPhase_paste_mul_star]
  simp_rw [character_sum]
  let d := liftBits x - liftBits x'
  let e := y - y'
  let a : Fin 5 → ZMod 3 → ℂ := fun i t =>
    ZMod.stdAddChar (alpha (select p) (outside p) d e i * t)
  let b : Fin 5 → ZMod 2 → ℂ := fun i t =>
    ZMod.stdAddChar (binaryCoeff (select p) (outside p) d i * t) *
      ZMod.stdAddChar (beta (select p) (outside p) d e i * liftBit t)
  let c := mixedPhase (paste p x 0) (paste p y 0) *
    star (mixedPhase (paste p x' 0) (paste p y' 0))
  change (∑ v : Fin 5 → ZMod 3, ∑ u : Fin 5 → ZMod 2,
    c * (∏ i, a i (v i)) *
      ((∏ i, ZMod.stdAddChar (binaryCoeff (select p) (outside p) d i * u i)) *
        ∏ i, ZMod.stdAddChar (beta (select p) (outside p) d e i * liftBit (u i)))) = _
  simp_rw [← Finset.prod_mul_distrib]
  change (∑ v : Fin 5 → ZMod 3, ∑ u : Fin 5 → ZMod 2,
    c * (∏ i, a i (v i)) * ∏ i, b i (u i)) = _
  simp_rw [← Finset.mul_sum]
  rw [← Fintype.prod_sum]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [← Fintype.prod_sum]
  change c * (∏ i, ∑ t : ZMod 3, a i t) * (∏ i, ∑ t : ZMod 2, b i t) = _
  have hb : (∏ i, ∑ t : ZMod 2, b i t) =
      ∏ i, ∑ t : Fin 2, (-1 : ℂ) ^ ((binaryCoeff (select p) (outside p) d i).val * t.val) *
        ZMod.stdAddChar (beta (select p) (outside p) d e i * (t.val : ZMod 3)) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [← (ZMod.finEquiv 2).toEquiv.sum_comp (b i)]
    apply Finset.sum_congr rfl
    intro t _
    simp only [b, binary_character_mul, liftBit]
    rfl
  rw [hb]
  dsimp only [environmentProduct, a, c, d, e]
  ring

/-- The finite certificate now implies vanishing of an actual environment sum. -/
theorem mixedPhase_environment_zero (p : Partition)
    (x x' : Fin 4 → ZMod 2) (y y' : Fin 4 → ZMod 3)
    (h : Cancels (select p) (outside p) (liftBits x - liftBits x') (y - y')) :
    (∑ v : Fin 5 → ZMod 3, ∑ u : Fin 5 → ZMod 2,
      mixedPhase (paste p x u) (paste p y v) *
        star (mixedPhase (paste p x' u) (paste p y' v))) = 0 := by
  rw [mixedPhase_environment_sum, environmentProduct_zero _ _ _ _ h, mul_zero]

end AME96

/- Actual reduced matrix entries, in FC's computational basis. -/
namespace AME96
open OpenQuantumProblem35
open scoped BigOperators

def CutCancellation (p : Partition) : Prop := ∀ d e : Difference,
  d ≠ 0 ∨ e ≠ 0 → Cancels (select p) (outside p) d e

def encode {n : ℕ} (x : Fin n → ZMod 2) (y : Fin n → ZMod 3) : Config n 6 :=
  fun i => localSixEquiv (x i, y i)

def rowBits {n : ℕ} (a : Config n 6) : Fin n → ZMod 2 :=
  fun i => (localSixEquiv.symm (a i)).1

def rowTrits {n : ℕ} (a : Config n 6) : Fin n → ZMod 3 :=
  fun i => (localSixEquiv.symm (a i)).2

@[simp] theorem encode_decode {n : ℕ} (a : Config n 6) :
    encode (rowBits a) (rowTrits a) = a := by funext i; simp [encode, rowBits, rowTrits]

@[simp] theorem rowBits_encode {n : ℕ} (x : Fin n → ZMod 2) (y : Fin n → ZMod 3) :
    rowBits (encode x y) = x := by funext i; simp [rowBits, encode]

@[simp] theorem rowTrits_encode {n : ℕ} (x : Fin n → ZMod 2) (y : Fin n → ZMod 3) :
    rowTrits (encode x y) = y := by funext i; simp [rowTrits, encode]

@[simp] theorem rowBits_paste (p : Partition) (a : Config 4 6) (z : Config 5 6) :
    rowBits (paste p a z) = paste p (rowBits a) (rowBits z) := by
  funext i
  obtain ⟨i, rfl⟩ := p.surjective i
  cases i <;> simp [rowBits] <;> rfl

@[simp] theorem rowTrits_paste (p : Partition) (a : Config 4 6) (z : Config 5 6) :
    rowTrits (paste p a z) = paste p (rowTrits a) (rowTrits z) := by
  funext i
  obtain ⟨i, rfl⟩ := p.surjective i
  cases i <;> simp [rowTrits] <;> rfl

theorem amplitude_eq_mixedPhase (a : Config 9 6) :
    amplitude a = coefficient * mixedPhase (rowBits a) (rowTrits a) := by
  have hb : bits a = rowBits a := by
    funext i
    change ((rowBits a i).val : ZMod 2) = rowBits a i
    exact ZMod.natCast_zmod_val (rowBits a i)
  have ht : trits a = rowTrits a := by
    funext i
    change ((rowTrits a i).val : ZMod 3) = rowTrits a i
    exact ZMod.natCast_zmod_val (rowTrits a i)
  have hl : liftedBits a = liftBits (rowBits a) := rfl
  simp only [amplitude, mixedPhase, ternaryPolynomial, ternaryPhase, bilinear, hb, ht, hl]
  ring

def environmentEquiv : ((Fin 5 → ZMod 3) × (Fin 5 → ZMod 2)) ≃ Config 5 6 where
  toFun v := encode v.2 v.1
  invFun z := (rowTrits z, rowBits z)
  left_inv v := by simp
  right_inv z := encode_decode z

theorem liftBit_injective : Function.Injective liftBit := by decide +kernel

theorem row_difference_nonzero (a b : Config 4 6) (h : a ≠ b) :
    liftBits (rowBits a) - liftBits (rowBits b) ≠ 0 ∨ rowTrits a - rowTrits b ≠ 0 := by
  by_contra hn
  push Not at hn
  have ht := sub_eq_zero.mp hn.2
  have hb : rowBits a = rowBits b := by
    funext i
    apply liftBit_injective
    exact congrFun (sub_eq_zero.mp hn.1) i
  apply h
  rw [← encode_decode a, ← encode_decode b, hb, ht]

/-- The actual off-diagonal reduced entry vanishes for every ordered cut. -/
theorem reduction_off_diagonal (p : Partition) (a b : Config 4 6) (hab : a ≠ b) (hc : CutCancellation p) :
    (∑ z : Config 5 6, amplitude (paste p a z) * star (amplitude (paste p b z))) = 0 := by
  rw [← environmentEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [amplitude_eq_mixedPhase, rowBits_paste, rowTrits_paste,
    environmentEquiv, Equiv.coe_fn_mk, rowBits_encode, rowTrits_encode]
  have regroup (r u v : ℂ) : r * u * star (r * v) =
      (r * star r) * (u * star v) := by simp only [star_mul]; ring
  simp_rw [regroup, ← Finset.mul_sum]
  rw [mixedPhase_environment_zero p (rowBits a) (rowBits b) (rowTrits a) (rowTrits b)
    (hc _ _ (row_difference_nonzero a b hab)), mul_zero]

theorem amplitude_mul_star (z : Config 9 6) :
    amplitude z * star (amplitude z) = ((6 : ℂ) ^ 9)⁻¹ := by
  change amplitude z * (starRingEnd ℂ) (amplitude z) = _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, amplitude_norm_sq]
  norm_cast
  norm_num

/-- Equal-index entries have 6^5 equal terms, each of squared modulus 6^-9. -/
theorem reduction_diagonal (p : Partition) (a : Config 4 6) :
    (∑ z : Config 5 6, amplitude (paste p a z) * star (amplitude (paste p a z))) =
      (1296 : ℂ)⁻¹ := by
  simp only [amplitude_mul_star, Finset.sum_const, Finset.card_univ, card_config, nsmul_eq_mul]
  norm_num

theorem reduction_eq (p : Partition) (a b : Config 4 6) (hc : CutCancellation p) :
    (∑ z : Config 5 6, amplitude (paste p a z) * star (amplitude (paste p b z))) =
      if a = b then (1296 : ℂ)⁻¹ else 0 := by
  split_ifs with h
  · subst b; exact reduction_diagonal p a
  · exact reduction_off_diagonal p a b h hc

end AME96




/- Closing the original, pinned FC existence statement with the explicit state. -/
namespace AME96
open OpenQuantumProblem35
open scoped BigOperators

noncomputable def standardPartition : Partition := Equiv.ofBijective
  (Sum.elim (leftIndex (m := 4) (n := 9) (by decide))
    (rightIndex (m := 4) (n := 9) (by decide))) (by decide +kernel)

noncomputable def permutedPartition (π : Equiv.Perm (Fin 9)) : Partition :=
  standardPartition.trans π.symm

theorem permuted_combine (π : Equiv.Perm (Fin 9)) (a : Config 4 6) (z : Config 5 6) :
    permuteConfig π (combineFirst 4 (n := 9) (by decide) a z) =
      paste (permutedPartition π) a z := by
  funext i
  obtain ⟨t, rfl⟩ := (permutedPartition π).surjective i
  cases t with
  | inl j =>
      rw [paste_left]
      change combineFirst 4 (by decide) a z (π (π.symm (leftIndex (m := 4) (n := 9) (by decide) j))) = a j
      simp
  | inr j =>
      rw [paste_right]
      change combineFirst 4 (by decide) a z (π (π.symm (rightIndex (m := 4) (n := 9) (by decide) j))) = z j
      simp

/-- The supplied state is AME in FC's exact definition, with every permutation covered. -/
theorem state_isAME_of_cancellation (hc : ∀ p : Partition, CutCancellation p) : IsAME state := by
  refine ⟨state_normalized, ?_⟩
  intro π
  unfold HasMaximallyMixedFirstReduction
  ext a b
  change (∑ z : Config 5 6,
    amplitude (permuteConfig π (combineFirst 4 (by decide) a z)) *
      star (amplitude (permuteConfig π (combineFirst 4 (by decide) b z)))) = _
  simp only [permuted_combine]
  rw [reduction_eq _ _ _ (hc _), maximallyMixed_apply, card_config]
  norm_num

end AME96

#print axioms AME96.state_isAME_of_cancellation
