import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-!
# AME(9,6): standalone Lean4Web proof

Mathlib-only edition of the pinned Formal Conjectures target. The AME
definitions below are extracted from FormalConjectures/OpenQuantumProblems/35.lean
at commit 2a46c7bd74505b85f4967475bb733ded0ef8d348. FC metadata is omitted.
The explicit witness and proof are generated from ../lean/AME96/*.lean.
-/

-- `answer(True)` is the proposition `True` at the target, as in FC's
-- default answer elaboration. The local macro supplies its surface syntax.
macro "answer(" p:term ")" : term => `($p)

#eval Lean.versionString
#guard Lean.versionString == "4.35.0-rc2"

open scoped BigOperators

namespace OpenQuantumProblem35

/- ## Basic structures -/

/-- A computational-basis configuration of $n$ parties with local dimension $d$. -/
abbrev Config (n d : ℕ) := Fin n → Fin d

/-- A state vector in the computational basis, viewed as a finite-dimensional Hilbert space. -/
abbrev StateVector (n d : ℕ) := EuclideanSpace ℂ (Config n d)

/-- Build a state vector from its computational-basis amplitudes. -/
abbrev mkStateVector {n d : ℕ} (ψ : Config n d → ℂ) : StateVector n d :=
  WithLp.toLp 2 ψ

/-- A state vector can be evaluated on a computational-basis configuration to read its amplitude. -/
instance {n d : ℕ} : CoeFun (StateVector n d) (fun _ => Config n d → ℂ) where
  coe ψ := ψ.ofLp

/-- A state built from amplitudes has those amplitudes as its coordinates. -/
@[simp]
lemma mkStateVector_apply {n d : ℕ} (ψ : Config n d → ℂ) (x : Config n d) :
    mkStateVector ψ x = ψ x := rfl

/-- A state vector is normalized if it has $L^2$ norm $1$. -/
def IsNormalized {n d : ℕ} (ψ : StateVector n d) : Prop :=
  ‖ψ‖ = 1

/-- A state is normalized iff its squared $L^2$ norm is $1$. -/
lemma isNormalized_iff_norm_sq_eq_one {n d : ℕ} (ψ : StateVector n d) :
    IsNormalized ψ ↔ ‖ψ‖ ^ 2 = 1 := by
  constructor
  · intro h
    rw [IsNormalized] at h
    calc
      ‖ψ‖ ^ 2 = (1 : ℝ) ^ 2 := by rw [h]
      _ = 1 := by norm_num
  · intro h
    rw [IsNormalized]
    have hsq : ‖ψ‖ ^ 2 = (1 : ℝ) ^ 2 := by
      simpa using h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hnorm | hnorm
    · exact hnorm
    · have hnonneg : 0 ≤ ‖ψ‖ := norm_nonneg ψ
      have : False := by
        linarith
      exact False.elim this

/-- Permute the parties of a configuration. -/
def permuteConfig {n d : ℕ} (π : Equiv.Perm (Fin n)) (x : Config n d) : Config n d :=
  fun i => x (π i)

/-- The identity permutation leaves a configuration unchanged. -/
theorem permuteConfig_refl {n d : ℕ} (x : Config n d) :
    permuteConfig (Equiv.refl (Fin n)) x = x := by
  ext i
  simp [permuteConfig]

/-- Permute the parties of a state vector. -/
def permuteState {n d : ℕ} (π : Equiv.Perm (Fin n)) (ψ : StateVector n d) : StateVector n d :=
  mkStateVector fun x => ψ (permuteConfig π x)

/-- Evaluating a permuted state vector reads the amplitude at the permuted configuration. -/
@[simp]
lemma permuteState_apply {n d : ℕ} (π : Equiv.Perm (Fin n)) (ψ : StateVector n d) (x : Config n d) :
    permuteState π ψ x = ψ (permuteConfig π x) := by
  rw [permuteState, mkStateVector_apply]

/-- The identity permutation leaves a state vector unchanged. -/
theorem permuteState_refl {n d : ℕ} (ψ : StateVector n d) :
    permuteState (Equiv.refl (Fin n)) ψ = ψ := by
  ext x
  simp [permuteState_apply, permuteConfig_refl]

/--
Merge a configuration on the first $m$ parties and a configuration on the remaining $n-m$
parties into a configuration on all $n$ parties.
-/
def combineFirst {n d : ℕ} (m : ℕ) (hm : m ≤ n)
    (x : Config m d) (y : Config (n - m) d) : Config n d :=
  fun i =>
    if hi : i.1 < m then
      x ⟨i.1, hi⟩
    else
      y ⟨i.1 - m, by
        have him : m ≤ i.1 := Nat.le_of_not_gt hi
        omega⟩

/-- The embedding of the first $m$ indices into $\mathrm{Fin}\, n$. -/
def leftIndex {m n : ℕ} (hm : m ≤ n) (i : Fin m) : Fin n :=
  ⟨i.1, lt_of_lt_of_le i.2 hm⟩

/-- The embedding of the last $n-m$ indices into $\mathrm{Fin}\, n$. -/
def rightIndex {m n : ℕ} (hm : m ≤ n) (i : Fin (n - m)) : Fin n :=
  ⟨m + i.1, by omega⟩

/-- Combining and then restricting to the left block recovers the left input. -/
@[simp]
lemma combineFirst_leftIndex {n d m : ℕ} (hm : m ≤ n)
    (x : Config m d) (y : Config (n - m) d) (i : Fin m) :
    combineFirst (n := n) (d := d) m hm x y (leftIndex hm i) = x i := by
  simp [combineFirst, leftIndex, i.2]

/-- Combining and then restricting to the right block recovers the right input. -/
@[simp]
lemma combineFirst_rightIndex {n d m : ℕ} (hm : m ≤ n)
    (x : Config m d) (y : Config (n - m) d) (i : Fin (n - m)) :
    combineFirst (n := n) (d := d) m hm x y (rightIndex hm i) = y i := by
  have hnot : ¬ m + i.1 < m := by omega
  simp [combineFirst, rightIndex, hnot]

/- ## Reduced density matrices and AME -/

/--
The reduced density matrix obtained by tracing out the last $n-m$ parties.

The subsystem is always the first $m$ parties; different subsystems are handled by first
permuting the parties.
-/
noncomputable def reducedDensityFirst {n d : ℕ} (m : ℕ) (hm : m ≤ n) (ψ : StateVector n d) :
    Matrix (Config m d) (Config m d) ℂ :=
  fun x y =>
    ∑ z : Config (n - m) d,
      ψ (combineFirst (n := n) (d := d) m hm x z) *
        star (ψ (combineFirst (n := n) (d := d) m hm y z))

/-- The maximally mixed state on $m$ parties. -/
noncomputable def maximallyMixed (m d : ℕ) :
    Matrix (Config m d) (Config m d) ℂ :=
  ((Fintype.card (Config m d) : ℂ)⁻¹) •
    (1 : Matrix (Config m d) (Config m d) ℂ)

/-- A state has maximally mixed reduction on the first $m$ parties. -/
def HasMaximallyMixedFirstReduction {n d : ℕ} (m : ℕ) (hm : m ≤ n)
    (ψ : StateVector n d) : Prop :=
  reducedDensityFirst (n := n) (d := d) m hm ψ = maximallyMixed m d

/--
A state $\psi$ is absolutely maximally entangled.

Standard AME definitions quantify over all subsets $A \subseteq \mathrm{Fin}\, n$ with
$|A| \le \lfloor n/2 \rfloor$ and require that the reduction on $A$ be maximally mixed.
For pure states it is enough to check subsets of size exactly $\lfloor n/2 \rfloor$; see the
references of Helwig--Cui--Riera--Latorre--Lo (2012) and
Goyeneche--Alsina--Latorre--Riera--Życzkowski (2015). In this file, a subsystem of that size is
encoded by first permuting the chosen parties to the front and then tracing out the remaining
parties.

We also require $\psi$ to be normalized explicitly.
-/
def IsAME {n d : ℕ} (ψ : StateVector n d) : Prop :=
  IsNormalized ψ ∧
    ∀ π : Equiv.Perm (Fin n),
      HasMaximallyMixedFirstReduction (n := n) (d := d)
        (n / 2) (Nat.div_le_self n 2) (permuteState π ψ)

/-- Existence of an $\mathrm{AME}(n,d)$ state. -/
def ExistsAME (n d : ℕ) : Prop :=
  ∃ ψ : StateVector n d, IsAME (n := n) (d := d) ψ

/-- The number of computational-basis configurations on $m$ parties of local dimension $d$ is $d^m$. -/
@[simp]
lemma card_config (m d : ℕ) : Fintype.card (Config m d) = d ^ m := by
  simp [Config]

/-- The matrix entries of the maximally mixed state are diagonal and equal to the inverse subsystem dimension. -/
lemma maximallyMixed_apply {m d : ℕ} (x y : Config m d) :
    maximallyMixed m d x y =
      if x = y then ((Fintype.card (Config m d) : ℂ)⁻¹) else 0 := by
  by_cases h : x = y
  · subst h
    simp [maximallyMixed]
  · simp [maximallyMixed, h]


end OpenQuantumProblem35


/-! ## Inlined proof module: AME96.Data -/


/-! Exact data from AME_9_6_complete_proof_20260922.md.
Generated by scripts/generate_data.py. No numerical approximations. -/
set_option maxRecDepth 8192
namespace AME96
open scoped BigOperators

def G : Matrix (Fin 9) (Fin 9) (ZMod 2) :=
  ![![0, 1, 1, 1, 1, 1, 1, 1, 1],
  ![1, 0, 0, 0, 0, 1, 0, 1, 1],
  ![1, 0, 0, 0, 0, 1, 1, 1, 0],
  ![1, 0, 0, 0, 1, 0, 1, 0, 1],
  ![1, 0, 0, 1, 0, 0, 0, 1, 1],
  ![1, 1, 1, 0, 0, 0, 1, 1, 1],
  ![1, 0, 1, 1, 0, 1, 0, 0, 1],
  ![1, 1, 1, 0, 1, 1, 0, 0, 0],
  ![1, 1, 0, 1, 1, 1, 1, 0, 0]]

def B : Matrix (Fin 9) (Fin 9) (ZMod 3) :=
  ![![0, 0, 2, 1, 2, 1, 0, 0, 2],
  ![0, 0, 1, 0, 0, 1, 1, 1, 1],
  ![0, 2, 0, 1, 0, 1, 0, 1, 1],
  ![1, 0, 0, 0, 2, 1, 2, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0]]

def H : Matrix (Fin 9) (Fin 9) (ZMod 3) :=
  ![![0, 2, 1, 0, 0, 0, 0, 0, 0],
  ![2, 0, 0, 1, 0, 0, 0, 0, 0],
  ![1, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 1, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0]]

def C : Matrix (Fin 9) (Fin 9) (ZMod 3) :=
  ![![0, 2, 0, 0, 0, 2, 1, 2, 1],
  ![2, 0, 0, 2, 1, 2, 0, 1, 0],
  ![0, 0, 0, 0, 1, 2, 0, 1, 1],
  ![0, 2, 0, 0, 0, 1, 0, 1, 1],
  ![0, 1, 1, 0, 0, 1, 2, 2, 1],
  ![2, 2, 2, 1, 1, 0, 1, 2, 1],
  ![1, 0, 0, 0, 2, 1, 0, 1, 1],
  ![2, 1, 1, 1, 2, 2, 1, 0, 1],
  ![1, 0, 1, 1, 1, 1, 1, 1, 0]]

theorem G_symmetric (i j : Fin 9) : G i j = G j i := by
  fin_cases i <;> fin_cases j <;> rfl
theorem G_diagonal : ∀ i, G i i = 0 := by decide +kernel
theorem H_symmetric (i j : Fin 9) : H i j = H j i := by
  fin_cases i <;> fin_cases j <;> rfl
theorem H_diagonal : ∀ i, H i i = 0 := by decide +kernel
theorem C_symmetric (i j : Fin 9) : C i j = C j i := by
  fin_cases i <;> fin_cases j <;> rfl
theorem C_diagonal : ∀ i, C i i = 0 := by decide +kernel

end AME96


/-! ## Inlined proof module: AME96.Phase -/


/-! Exact one-coordinate phase sums for the mixed binary–ternary construction. -/
namespace AME96
open scoped BigOperators

/-- A nontrivial ternary additive character sums to zero. -/
theorem ternary_sum (a : ZMod 3) :
    (∑ y : ZMod 3, ZMod.stdAddChar (a * y)) =
      if a = 0 then (3 : ℂ) else 0 := by
  by_cases ha : a = 0
  · simp [ha, ZMod.card]
  · simpa [ha] using
      (AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar 3 ha))

theorem ternary_cancel (a : ZMod 3) (ha : a ≠ 0) :
    (∑ y : ZMod 3, ZMod.stdAddChar (a * y)) = 0 := by
  simp [ternary_sum, ha]

/-- The binary sum may also carry a ternary phase. -/
theorem binary_sum (r : ZMod 2) (b : ZMod 3) :
    (∑ x : Fin 2, (-1 : ℂ) ^ (r.val * x.val) *
      ZMod.stdAddChar (b * (x.val : ZMod 3))) =
      1 + (-1 : ℂ) ^ r.val * ZMod.stdAddChar b := by
  simp [Fin.sum_univ_succ]

theorem binary_cancel (r : ZMod 2) (b : ZMod 3)
    (hr : r = 1) (hb : b = 0) :
    (∑ x : Fin 2, (-1 : ℂ) ^ (r.val * x.val) *
      ZMod.stdAddChar (b * (x.val : ZMod 3))) = 0 := by
  rw [binary_sum, hr, hb]
  change 1 + (-1 : ℂ) ^ 1 * ZMod.stdAddChar (0 : ZMod 3) = 0
  norm_num

theorem character_mul_star {N : ℕ} [NeZero N] (a b : ZMod N) :
    ZMod.stdAddChar a * star (ZMod.stdAddChar b) =
      ZMod.stdAddChar (a - b) := by
  change ZMod.stdAddChar a * (starRingEnd ℂ) (ZMod.stdAddChar b) = _
  rw [← AddChar.map_neg_eq_conj]
  simpa [sub_eq_add_neg] using
    (AddChar.map_add_eq_mul ZMod.stdAddChar a (-b)).symm

theorem character_norm {N : ℕ} [NeZero N] (a : ZMod N) :
    ‖ZMod.stdAddChar a‖ = 1 := by
  change ‖(↑(ZMod.toCircle a) : ℂ)‖ = 1
  exact Circle.norm_coe _

end AME96


/-! ## Inlined proof module: AME96.Finite -/


/-! Exact finite coefficients for the mixed binary–ternary cancellation criterion. -/
namespace AME96
open scoped BigOperators

abbrev Difference := Fin 4 → ZMod 3
abbrev Selected := Fin 4 → Fin 9
abbrev Outside := Fin 5 → Fin 9

def alpha (s : Selected) (o : Outside) (d e : Difference) (i : Fin 5) : ZMod 3 :=
  ∑ j, (C (o i) (s j) * e j + B (s j) (o i) * d j)

def binaryCoeff (s : Selected) (o : Outside) (d : Difference) (i : Fin 5) : ZMod 2 :=
  ∑ j, G (o i) (s j) * (if d j = 0 then 0 else 1)

def beta (s : Selected) (o : Outside) (d e : Difference) (i : Fin 5) : ZMod 3 :=
  ∑ j, (B (o i) (s j) * e j + H (o i) (s j) * d j)

/-- Exact sufficient condition for an off-diagonal entry to vanish. -/
def Cancels (s : Selected) (o : Outside) (d e : Difference) : Prop :=
  (∃ i, alpha s o d e i ≠ 0) ∨
  (∃ i, binaryCoeff s o d i = 1 ∧ beta s o d e i = 0)

instance (s : Selected) (o : Outside) (d e : Difference) :
    Decidable (Cancels s o d e) := by
  unfold Cancels
  infer_instance

def firstSelected : Selected := ![0, 1, 2, 3]
def firstOutside : Outside := ![4, 5, 6, 7, 8]

end AME96


/-! ## Inlined proof module: AME96.FirstCut -/


namespace AME96

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
/-- All 3^8 - 1 nonzero difference types on the cut {0,1,2,3}. -/
theorem firstCut_cancels : ∀ d e : Difference,
    d ≠ 0 ∨ e ≠ 0 → Cancels firstSelected firstOutside d e := by
  decide +kernel

end AME96

#print axioms AME96.firstCut_cancels


/-! ## Inlined proof module: AME96.Factor -/


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


/-! ## Inlined proof module: AME96.Polynomial -/


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


/-! ## Inlined proof module: AME96.Partition -/


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


/-! ## Inlined proof module: AME96.MixedPhase -/


/-! Exact phase differences for the supplied mixed binary–ternary state. -/
namespace AME96
open scoped BigOperators

def liftBit (x : ZMod 2) : ZMod 3 := x.val

def liftBits {n : ℕ} (x : Fin n → ZMod 2) : Fin n → ZMod 3 := fun i => liftBit (x i)

@[simp] theorem liftBit_zero : liftBit 0 = 0 := rfl

@[simp] theorem liftBits_paste (p : Partition) (x : Fin 4 → ZMod 2) (u : Fin 5 → ZMod 2) :
    liftBits (paste p x u) = paste p (liftBits x) (liftBits u) := by
  funext i
  obtain ⟨i, rfl⟩ := p.surjective i
  cases i <;> simp [liftBits]

/-- A signed difference modulo 3 records exactly whether two bits differ. -/
theorem bit_sub_eq_indicator : ∀ x x' : ZMod 2,
    x - x' = if liftBit x - liftBit x' = 0 then 0 else 1 := by decide +kernel

def ternaryPolynomial (x y : Fin 9 → ZMod 3) : ZMod 3 :=
  quadratic C y + bilinear B x y + quadratic H x

noncomputable def mixedPhase (x : Fin 9 → ZMod 2) (y : Fin 9 → ZMod 3) : ℂ :=
  ZMod.stdAddChar (quadratic G x) * ZMod.stdAddChar (ternaryPolynomial (liftBits x) y)

def select (p : Partition) : Selected := fun j => p (.inl j)
def outside (p : Partition) : Outside := fun i => p (.inr i)

theorem binary_paste_difference (p : Partition) (x x' : Fin 4 → ZMod 2)
    (u : Fin 5 → ZMod 2) :
    quadratic G (paste p x u) - quadratic G (paste p x' u) =
      (quadratic G (paste p x 0) - quadratic G (paste p x' 0)) +
      ∑ i, binaryCoeff (select p) (outside p) (liftBits x - liftBits x') i * u i := by
  rw [quadratic_paste_difference G G_symmetric G_diagonal]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [binaryCoeff, select, outside, Pi.sub_apply, liftBits, bit_sub_eq_indicator]
  rw [mul_comm]
  rfl

theorem ternary_paste_difference (p : Partition)
    (x x' y y' : Fin 4 → ZMod 3) (u v : Fin 5 → ZMod 3) :
    ternaryPolynomial (paste p x u) (paste p y v) -
      ternaryPolynomial (paste p x' u) (paste p y' v) =
      (ternaryPolynomial (paste p x 0) (paste p y 0) -
        ternaryPolynomial (paste p x' 0) (paste p y' 0)) +
      (∑ i, alpha (select p) (outside p) (x - x') (y - y') i * v i) +
      (∑ i, beta (select p) (outside p) (x - x') (y - y') i * u i) := by
  have hC := quadratic_paste_difference C C_symmetric C_diagonal p y y' v
  have hH := quadratic_paste_difference H H_symmetric H_diagonal p x x' u
  have hB := bilinear_paste_difference B p x x' y y' u v
  simp only [ternaryPolynomial]
  simp only [alpha, beta, select, outside, Pi.sub_apply, Finset.sum_add_distrib,
    add_mul, Finset.sum_mul, Finset.mul_sum] at *
  simp only [mul_comm] at *
  linear_combination hC + hB + hH

/-- Before summing over environments, each amplitude product splits into local phases. -/
theorem mixedPhase_paste_mul_star (p : Partition)
    (x x' : Fin 4 → ZMod 2) (y y' : Fin 4 → ZMod 3)
    (u : Fin 5 → ZMod 2) (v : Fin 5 → ZMod 3) :
    mixedPhase (paste p x u) (paste p y v) *
      star (mixedPhase (paste p x' u) (paste p y' v)) =
      (mixedPhase (paste p x 0) (paste p y 0) *
        star (mixedPhase (paste p x' 0) (paste p y' 0))) *
      ZMod.stdAddChar (∑ i, alpha (select p) (outside p)
        (liftBits x - liftBits x') (y - y') i * v i) *
      (ZMod.stdAddChar (∑ i, binaryCoeff (select p) (outside p)
          (liftBits x - liftBits x') i * u i) *
        ZMod.stdAddChar (∑ i, beta (select p) (outside p)
          (liftBits x - liftBits x') (y - y') i * liftBit (u i))) := by
  have regroup (a b c d : ℂ) : a * b * star (c * d) =
      (a * star c) * (b * star d) := by simp only [star_mul]; ring
  simp only [mixedPhase, regroup, character_mul_star, liftBits_paste]
  rw [binary_paste_difference, ternary_paste_difference]
  have hzero : liftBits (0 : Fin 5 → ZMod 2) = 0 := by ext i; rfl
  simp only [hzero, AddChar.map_add_eq_mul, liftBits]
  ring

end AME96


/-! ## Inlined proof module: AME96.CharacterSum -/


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


/-! ## Inlined proof module: AME96.Certificate -/


/-! A small, kernel-checkable certificate for each cut. -/
namespace AME96
open scoped BigOperators
open Matrix

def cBlock (s : Selected) (o : Outside) : Matrix (Fin 5) (Fin 4) (ZMod 3) :=
  fun i j => C (o i) (s j)

def tBlock (s : Selected) (o : Outside) : Matrix (Fin 5) (Fin 4) (ZMod 3) :=
  fun i j => B (s j) (o i)

def compatible (s : Selected) (o : Outside)
    (L : Matrix (Fin 4) (Fin 5) (ZMod 3)) (d : Difference) : Difference :=
  -(L *ᵥ (tBlock s o *ᵥ d))

theorem alpha_eq_mulVec (s : Selected) (o : Outside) (d e : Difference) :
    alpha s o d e = cBlock s o *ᵥ e + tBlock s o *ᵥ d := by
  ext i
  simp [alpha, cBlock, tBlock, Matrix.mulVec, dotProduct, Finset.sum_add_distrib]

theorem compatible_of_alpha_zero (s : Selected) (o : Outside)
    (L : Matrix (Fin 4) (Fin 5) (ZMod 3))
    (hL : L * cBlock s o = 1) (d e : Difference)
    (ha : alpha s o d e = 0) : e = compatible s o L d := by
  rw [alpha_eq_mulVec] at ha
  have h := congrArg (fun v => L *ᵥ v) ha
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, hL,
    Matrix.one_mulVec, Matrix.mulVec_zero] at h
  simpa only [compatible, Matrix.mulVec_mulVec] using (eq_neg_of_add_eq_zero_left h)

theorem cancels_of_certificate (s : Selected) (o : Outside)
    (L : Matrix (Fin 4) (Fin 5) (ZMod 3))
    (hL : L * cBlock s o = 1)
    (hcheck : ∀ d : Difference, d ≠ 0 → Cancels s o d (compatible s o L d)) :
    ∀ d e : Difference, d ≠ 0 ∨ e ≠ 0 → Cancels s o d e := by
  intro d e hde
  by_cases ha : alpha s o d e = 0
  · have he := compatible_of_alpha_zero s o L hL d e ha
    have hd : d ≠ 0 := by
      intro hd
      have he0 : e = 0 := by simpa [compatible, hd] using he
      exact hde.elim (fun h => h hd) (fun h => h he0)
    rw [he]
    exact hcheck d hd
  · left
    simpa only [funext_iff, Pi.zero_apply, not_forall] using ha

theorem cancels_of_small_certificate (s : Selected) (o : Outside)
    (L : Matrix (Fin 4) (Fin 5) (ZMod 3))
    (E : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hL : L * cBlock s o = 1) (hE : L * tBlock s o = -E)
    (hcheck : ∀ d : Difference, d ≠ 0 → Cancels s o d (E *ᵥ d)) :
    ∀ d e : Difference, d ≠ 0 ∨ e ≠ 0 → Cancels s o d e := by
  apply cancels_of_certificate s o L hL
  intro d hd
  have he : compatible s o L d = E *ᵥ d := by
    simp only [compatible, Matrix.mulVec_mulVec, hE, Matrix.neg_mulVec, neg_neg]
  rw [he]
  exact hcheck d hd

end AME96


/-! ## Inlined proof module: AME96.CutData -/


/-! Generated by scripts/generate_cuts.py. All certificates are checked in AllCuts.lean. -/
set_option maxRecDepth 65536
namespace AME96

def cutSelected : Fin 126 → Selected :=
  ![![0, 1, 2, 3],
    ![0, 1, 2, 4],
    ![0, 1, 2, 5],
    ![0, 1, 2, 6],
    ![0, 1, 2, 7],
    ![0, 1, 2, 8],
    ![0, 1, 3, 4],
    ![0, 1, 3, 5],
    ![0, 1, 3, 6],
    ![0, 1, 3, 7],
    ![0, 1, 3, 8],
    ![0, 1, 4, 5],
    ![0, 1, 4, 6],
    ![0, 1, 4, 7],
    ![0, 1, 4, 8],
    ![0, 1, 5, 6],
    ![0, 1, 5, 7],
    ![0, 1, 5, 8],
    ![0, 1, 6, 7],
    ![0, 1, 6, 8],
    ![0, 1, 7, 8],
    ![0, 2, 3, 4],
    ![0, 2, 3, 5],
    ![0, 2, 3, 6],
    ![0, 2, 3, 7],
    ![0, 2, 3, 8],
    ![0, 2, 4, 5],
    ![0, 2, 4, 6],
    ![0, 2, 4, 7],
    ![0, 2, 4, 8],
    ![0, 2, 5, 6],
    ![0, 2, 5, 7],
    ![0, 2, 5, 8],
    ![0, 2, 6, 7],
    ![0, 2, 6, 8],
    ![0, 2, 7, 8],
    ![0, 3, 4, 5],
    ![0, 3, 4, 6],
    ![0, 3, 4, 7],
    ![0, 3, 4, 8],
    ![0, 3, 5, 6],
    ![0, 3, 5, 7],
    ![0, 3, 5, 8],
    ![0, 3, 6, 7],
    ![0, 3, 6, 8],
    ![0, 3, 7, 8],
    ![0, 4, 5, 6],
    ![0, 4, 5, 7],
    ![0, 4, 5, 8],
    ![0, 4, 6, 7],
    ![0, 4, 6, 8],
    ![0, 4, 7, 8],
    ![0, 5, 6, 7],
    ![0, 5, 6, 8],
    ![0, 5, 7, 8],
    ![0, 6, 7, 8],
    ![1, 2, 3, 4],
    ![1, 2, 3, 5],
    ![1, 2, 3, 6],
    ![1, 2, 3, 7],
    ![1, 2, 3, 8],
    ![1, 2, 4, 5],
    ![1, 2, 4, 6],
    ![1, 2, 4, 7],
    ![1, 2, 4, 8],
    ![1, 2, 5, 6],
    ![1, 2, 5, 7],
    ![1, 2, 5, 8],
    ![1, 2, 6, 7],
    ![1, 2, 6, 8],
    ![1, 2, 7, 8],
    ![1, 3, 4, 5],
    ![1, 3, 4, 6],
    ![1, 3, 4, 7],
    ![1, 3, 4, 8],
    ![1, 3, 5, 6],
    ![1, 3, 5, 7],
    ![1, 3, 5, 8],
    ![1, 3, 6, 7],
    ![1, 3, 6, 8],
    ![1, 3, 7, 8],
    ![1, 4, 5, 6],
    ![1, 4, 5, 7],
    ![1, 4, 5, 8],
    ![1, 4, 6, 7],
    ![1, 4, 6, 8],
    ![1, 4, 7, 8],
    ![1, 5, 6, 7],
    ![1, 5, 6, 8],
    ![1, 5, 7, 8],
    ![1, 6, 7, 8],
    ![2, 3, 4, 5],
    ![2, 3, 4, 6],
    ![2, 3, 4, 7],
    ![2, 3, 4, 8],
    ![2, 3, 5, 6],
    ![2, 3, 5, 7],
    ![2, 3, 5, 8],
    ![2, 3, 6, 7],
    ![2, 3, 6, 8],
    ![2, 3, 7, 8],
    ![2, 4, 5, 6],
    ![2, 4, 5, 7],
    ![2, 4, 5, 8],
    ![2, 4, 6, 7],
    ![2, 4, 6, 8],
    ![2, 4, 7, 8],
    ![2, 5, 6, 7],
    ![2, 5, 6, 8],
    ![2, 5, 7, 8],
    ![2, 6, 7, 8],
    ![3, 4, 5, 6],
    ![3, 4, 5, 7],
    ![3, 4, 5, 8],
    ![3, 4, 6, 7],
    ![3, 4, 6, 8],
    ![3, 4, 7, 8],
    ![3, 5, 6, 7],
    ![3, 5, 6, 8],
    ![3, 5, 7, 8],
    ![3, 6, 7, 8],
    ![4, 5, 6, 7],
    ![4, 5, 6, 8],
    ![4, 5, 7, 8],
    ![4, 6, 7, 8],
    ![5, 6, 7, 8]]

def cutOutside : Fin 126 → Outside :=
  ![![4, 5, 6, 7, 8],
    ![3, 5, 6, 7, 8],
    ![3, 4, 6, 7, 8],
    ![3, 4, 5, 7, 8],
    ![3, 4, 5, 6, 8],
    ![3, 4, 5, 6, 7],
    ![2, 5, 6, 7, 8],
    ![2, 4, 6, 7, 8],
    ![2, 4, 5, 7, 8],
    ![2, 4, 5, 6, 8],
    ![2, 4, 5, 6, 7],
    ![2, 3, 6, 7, 8],
    ![2, 3, 5, 7, 8],
    ![2, 3, 5, 6, 8],
    ![2, 3, 5, 6, 7],
    ![2, 3, 4, 7, 8],
    ![2, 3, 4, 6, 8],
    ![2, 3, 4, 6, 7],
    ![2, 3, 4, 5, 8],
    ![2, 3, 4, 5, 7],
    ![2, 3, 4, 5, 6],
    ![1, 5, 6, 7, 8],
    ![1, 4, 6, 7, 8],
    ![1, 4, 5, 7, 8],
    ![1, 4, 5, 6, 8],
    ![1, 4, 5, 6, 7],
    ![1, 3, 6, 7, 8],
    ![1, 3, 5, 7, 8],
    ![1, 3, 5, 6, 8],
    ![1, 3, 5, 6, 7],
    ![1, 3, 4, 7, 8],
    ![1, 3, 4, 6, 8],
    ![1, 3, 4, 6, 7],
    ![1, 3, 4, 5, 8],
    ![1, 3, 4, 5, 7],
    ![1, 3, 4, 5, 6],
    ![1, 2, 6, 7, 8],
    ![1, 2, 5, 7, 8],
    ![1, 2, 5, 6, 8],
    ![1, 2, 5, 6, 7],
    ![1, 2, 4, 7, 8],
    ![1, 2, 4, 6, 8],
    ![1, 2, 4, 6, 7],
    ![1, 2, 4, 5, 8],
    ![1, 2, 4, 5, 7],
    ![1, 2, 4, 5, 6],
    ![1, 2, 3, 7, 8],
    ![1, 2, 3, 6, 8],
    ![1, 2, 3, 6, 7],
    ![1, 2, 3, 5, 8],
    ![1, 2, 3, 5, 7],
    ![1, 2, 3, 5, 6],
    ![1, 2, 3, 4, 8],
    ![1, 2, 3, 4, 7],
    ![1, 2, 3, 4, 6],
    ![1, 2, 3, 4, 5],
    ![0, 5, 6, 7, 8],
    ![0, 4, 6, 7, 8],
    ![0, 4, 5, 7, 8],
    ![0, 4, 5, 6, 8],
    ![0, 4, 5, 6, 7],
    ![0, 3, 6, 7, 8],
    ![0, 3, 5, 7, 8],
    ![0, 3, 5, 6, 8],
    ![0, 3, 5, 6, 7],
    ![0, 3, 4, 7, 8],
    ![0, 3, 4, 6, 8],
    ![0, 3, 4, 6, 7],
    ![0, 3, 4, 5, 8],
    ![0, 3, 4, 5, 7],
    ![0, 3, 4, 5, 6],
    ![0, 2, 6, 7, 8],
    ![0, 2, 5, 7, 8],
    ![0, 2, 5, 6, 8],
    ![0, 2, 5, 6, 7],
    ![0, 2, 4, 7, 8],
    ![0, 2, 4, 6, 8],
    ![0, 2, 4, 6, 7],
    ![0, 2, 4, 5, 8],
    ![0, 2, 4, 5, 7],
    ![0, 2, 4, 5, 6],
    ![0, 2, 3, 7, 8],
    ![0, 2, 3, 6, 8],
    ![0, 2, 3, 6, 7],
    ![0, 2, 3, 5, 8],
    ![0, 2, 3, 5, 7],
    ![0, 2, 3, 5, 6],
    ![0, 2, 3, 4, 8],
    ![0, 2, 3, 4, 7],
    ![0, 2, 3, 4, 6],
    ![0, 2, 3, 4, 5],
    ![0, 1, 6, 7, 8],
    ![0, 1, 5, 7, 8],
    ![0, 1, 5, 6, 8],
    ![0, 1, 5, 6, 7],
    ![0, 1, 4, 7, 8],
    ![0, 1, 4, 6, 8],
    ![0, 1, 4, 6, 7],
    ![0, 1, 4, 5, 8],
    ![0, 1, 4, 5, 7],
    ![0, 1, 4, 5, 6],
    ![0, 1, 3, 7, 8],
    ![0, 1, 3, 6, 8],
    ![0, 1, 3, 6, 7],
    ![0, 1, 3, 5, 8],
    ![0, 1, 3, 5, 7],
    ![0, 1, 3, 5, 6],
    ![0, 1, 3, 4, 8],
    ![0, 1, 3, 4, 7],
    ![0, 1, 3, 4, 6],
    ![0, 1, 3, 4, 5],
    ![0, 1, 2, 7, 8],
    ![0, 1, 2, 6, 8],
    ![0, 1, 2, 6, 7],
    ![0, 1, 2, 5, 8],
    ![0, 1, 2, 5, 7],
    ![0, 1, 2, 5, 6],
    ![0, 1, 2, 4, 8],
    ![0, 1, 2, 4, 7],
    ![0, 1, 2, 4, 6],
    ![0, 1, 2, 4, 5],
    ![0, 1, 2, 3, 8],
    ![0, 1, 2, 3, 7],
    ![0, 1, 2, 3, 6],
    ![0, 1, 2, 3, 5],
    ![0, 1, 2, 3, 4]]

def cutLeftInverse : Fin 126 → Matrix (Fin 4) (Fin 5) (ZMod 3) :=
  ![![![0, 0, 1, 0, 0], ![2, 1, 2, 0, 2], ![2, 2, 1, 0, 1], ![1, 1, 1, 0, 0]],
    ![![0, 1, 0, 1, 0], ![2, 0, 0, 0, 0], ![1, 2, 2, 0, 0], ![0, 1, 2, 1, 0]],
    ![![0, 2, 2, 1, 0], ![2, 1, 2, 2, 0], ![1, 2, 2, 2, 0], ![0, 1, 2, 2, 0]],
    ![![0, 2, 2, 0, 0], ![2, 0, 0, 0, 0], ![1, 0, 1, 2, 0], ![0, 2, 1, 2, 0]],
    ![![0, 1, 1, 2, 0], ![2, 2, 2, 2, 0], ![1, 1, 0, 0, 0], ![0, 2, 2, 2, 0]],
    ![![0, 1, 0, 0, 2], ![2, 1, 2, 0, 1], ![1, 2, 2, 0, 1], ![0, 1, 2, 0, 1]],
    ![![1, 0, 1, 0, 0], ![1, 1, 0, 2, 0], ![1, 2, 1, 2, 0], ![1, 0, 0, 0, 0]],
    ![![1, 0, 1, 0, 0], ![1, 1, 0, 0, 0], ![2, 2, 1, 1, 0], ![2, 0, 0, 0, 0]],
    ![![0, 0, 2, 2, 2], ![0, 0, 1, 2, 0], ![0, 1, 0, 2, 2], ![0, 2, 1, 2, 0]],
    ![![2, 0, 0, 1, 0], ![1, 1, 0, 0, 0], ![1, 1, 1, 1, 0], ![1, 0, 0, 0, 0]],
    ![![2, 0, 0, 1, 0], ![2, 1, 0, 0, 0], ![0, 1, 1, 1, 0], ![1, 0, 0, 0, 0]],
    ![![1, 0, 1, 0, 0], ![1, 1, 2, 2, 0], ![2, 2, 2, 2, 0], ![1, 2, 2, 2, 0]],
    ![![0, 2, 1, 0, 2], ![0, 2, 0, 0, 0], ![1, 0, 0, 0, 0], ![2, 1, 2, 0, 2]],
    ![![1, 1, 2, 0, 0], ![0, 0, 2, 2, 0], ![1, 2, 1, 1, 0], ![0, 1, 2, 2, 0]],
    ![![1, 2, 1, 2, 0], ![0, 1, 1, 1, 0], ![1, 1, 2, 2, 0], ![0, 2, 1, 1, 0]],
    ![![1, 1, 2, 2, 0], ![2, 2, 0, 0, 0], ![2, 0, 0, 0, 0], ![1, 2, 2, 0, 0]],
    ![![2, 2, 2, 1, 0], ![1, 0, 1, 0, 0], ![0, 2, 2, 0, 0], ![1, 2, 2, 0, 0]],
    ![![0, 1, 1, 1, 0], ![0, 1, 2, 0, 0], ![1, 1, 1, 0, 0], ![2, 1, 1, 0, 0]],
    ![![1, 0, 2, 2, 0], ![1, 2, 0, 0, 0], ![0, 2, 2, 0, 0], ![1, 0, 0, 0, 0]],
    ![![2, 0, 2, 2, 0], ![1, 2, 0, 0, 0], ![2, 2, 2, 0, 0], ![1, 0, 0, 0, 0]],
    ![![1, 2, 1, 2, 0], ![1, 2, 0, 0, 0], ![1, 1, 1, 0, 0], ![0, 2, 2, 0, 0]],
    ![![2, 1, 2, 1, 0], ![2, 2, 1, 0, 0], ![2, 0, 2, 0, 0], ![2, 1, 1, 1, 0]],
    ![![1, 2, 0, 1, 0], ![1, 0, 2, 1, 0], ![2, 0, 2, 0, 0], ![2, 1, 1, 2, 0]],
    ![![1, 1, 1, 0, 0], ![0, 0, 1, 2, 0], ![1, 2, 2, 0, 0], ![0, 2, 1, 2, 0]],
    ![![2, 2, 2, 2, 0], ![1, 2, 1, 2, 0], ![1, 2, 2, 0, 0], ![1, 1, 1, 2, 0]],
    ![![2, 2, 2, 2, 0], ![2, 0, 2, 1, 0], ![0, 1, 1, 1, 0], ![1, 1, 1, 2, 0]],
    ![![1, 2, 0, 2, 1], ![0, 0, 0, 2, 2], ![2, 0, 0, 2, 1], ![0, 1, 0, 0, 0]],
    ![![1, 0, 0, 2, 1], ![2, 0, 1, 1, 1], ![2, 0, 0, 2, 1], ![1, 0, 2, 1, 1]],
    ![![2, 1, 2, 0, 2], ![1, 1, 2, 0, 0], ![0, 0, 2, 0, 2], ![0, 1, 0, 0, 0]],
    ![![0, 1, 1, 0, 1], ![1, 1, 2, 0, 0], ![1, 1, 1, 0, 1], ![0, 1, 0, 0, 0]],
    ![![2, 2, 0, 0, 0], ![1, 1, 2, 2, 0], ![0, 1, 0, 0, 0], ![1, 2, 1, 2, 0]],
    ![![0, 2, 0, 1, 0], ![1, 2, 1, 1, 0], ![1, 1, 0, 1, 0], ![2, 0, 0, 2, 0]],
    ![![0, 2, 0, 1, 0], ![0, 2, 1, 0, 0], ![2, 1, 0, 2, 0], ![1, 0, 0, 1, 0]],
    ![![2, 1, 0, 0, 0], ![2, 1, 2, 0, 2], ![2, 0, 1, 0, 2], ![0, 1, 0, 0, 0]],
    ![![2, 0, 0, 0, 0], ![1, 2, 2, 0, 2], ![1, 0, 1, 0, 2], ![0, 1, 0, 0, 0]],
    ![![1, 1, 1, 1, 0], ![1, 1, 0, 2, 0], ![2, 1, 1, 1, 0], ![1, 0, 2, 2, 0]],
    ![![0, 1, 1, 0, 0], ![2, 0, 2, 0, 0], ![1, 0, 2, 1, 0], ![1, 2, 2, 1, 0]],
    ![![0, 0, 1, 0, 2], ![2, 1, 2, 0, 1], ![0, 1, 0, 0, 0], ![1, 1, 0, 0, 1]],
    ![![2, 1, 2, 2, 0], ![0, 0, 1, 1, 0], ![1, 1, 1, 2, 0], ![2, 0, 2, 1, 0]],
    ![![1, 2, 2, 0, 2], ![1, 1, 0, 0, 2], ![0, 0, 2, 0, 1], ![0, 1, 1, 0, 2]],
    ![![1, 2, 1, 1, 0], ![1, 2, 2, 2, 0], ![0, 2, 0, 0, 0], ![0, 2, 2, 0, 0]],
    ![![2, 1, 0, 1, 2], ![0, 0, 0, 2, 1], ![2, 2, 0, 0, 2], ![2, 0, 0, 0, 2]],
    ![![0, 0, 2, 1, 0], ![2, 2, 2, 2, 0], ![0, 1, 2, 0, 0], ![0, 2, 2, 0, 0]],
    ![![1, 1, 1, 1, 0], ![1, 0, 2, 2, 0], ![0, 2, 2, 0, 0], ![0, 1, 0, 0, 0]],
    ![![1, 1, 1, 1, 0], ![1, 2, 2, 2, 0], ![0, 1, 2, 0, 0], ![0, 1, 0, 0, 0]],
    ![![1, 1, 1, 1, 0], ![1, 1, 0, 2, 0], ![0, 2, 1, 0, 0], ![0, 2, 2, 0, 0]],
    ![![2, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 0, 1, 0, 0], ![2, 2, 2, 1, 0]],
    ![![2, 1, 0, 0, 0], ![2, 1, 1, 2, 0], ![1, 0, 1, 1, 0], ![2, 0, 0, 2, 0]],
    ![![1, 1, 0, 2, 0], ![1, 1, 1, 1, 0], ![2, 0, 1, 2, 0], ![1, 0, 0, 1, 0]],
    ![![2, 1, 0, 0, 0], ![0, 1, 2, 0, 0], ![2, 0, 2, 1, 0], ![0, 0, 1, 0, 0]],
    ![![2, 1, 2, 0, 0], ![0, 1, 2, 0, 0], ![2, 0, 2, 1, 0], ![0, 0, 1, 0, 0]],
    ![![0, 1, 1, 0, 1], ![0, 1, 2, 0, 0], ![1, 0, 2, 0, 1], ![2, 0, 2, 0, 2]],
    ![![2, 1, 0, 0, 0], ![0, 1, 2, 0, 0], ![0, 2, 0, 2, 0], ![0, 2, 2, 0, 0]],
    ![![2, 2, 1, 0, 0], ![0, 1, 2, 0, 0], ![0, 0, 1, 2, 0], ![0, 2, 2, 0, 0]],
    ![![2, 2, 0, 1, 0], ![0, 1, 2, 0, 0], ![0, 0, 2, 1, 0], ![0, 2, 0, 2, 0]],
    ![![1, 1, 0, 1, 1], ![2, 2, 0, 0, 1], ![2, 1, 0, 1, 1], ![1, 0, 0, 2, 2]],
    ![![2, 0, 0, 0, 0], ![1, 1, 2, 2, 0], ![0, 2, 0, 2, 0], ![0, 0, 2, 0, 0]],
    ![![2, 0, 2, 0, 0], ![1, 1, 0, 0, 0], ![0, 2, 2, 1, 0], ![0, 0, 1, 0, 0]],
    ![![2, 2, 1, 2, 0], ![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 2, 1, 2, 0]],
    ![![2, 0, 0, 2, 0], ![1, 1, 0, 2, 0], ![0, 1, 1, 2, 0], ![0, 0, 0, 1, 0]],
    ![![2, 0, 0, 1, 0], ![1, 1, 0, 1, 0], ![0, 1, 1, 1, 0], ![0, 0, 0, 1, 0]],
    ![![1, 1, 0, 0, 0], ![1, 0, 2, 1, 0], ![1, 2, 2, 0, 0], ![1, 2, 0, 0, 0]],
    ![![0, 2, 0, 0, 0], ![0, 2, 1, 0, 2], ![2, 2, 2, 0, 2], ![1, 2, 0, 0, 0]],
    ![![1, 1, 0, 0, 0], ![2, 2, 2, 2, 0], ![1, 2, 0, 2, 0], ![1, 2, 0, 0, 0]],
    ![![2, 0, 2, 0, 2], ![1, 0, 1, 2, 2], ![0, 0, 2, 2, 2], ![0, 0, 2, 0, 2]],
    ![![2, 0, 1, 2, 0], ![1, 0, 1, 0, 0], ![2, 1, 1, 2, 0], ![2, 1, 2, 1, 0]],
    ![![1, 1, 0, 0, 0], ![2, 1, 0, 0, 1], ![2, 0, 2, 0, 1], ![2, 2, 1, 0, 2]],
    ![![0, 2, 0, 1, 0], ![0, 1, 1, 1, 0], ![1, 2, 0, 0, 0], ![2, 1, 0, 1, 0]],
    ![![0, 2, 1, 1, 0], ![1, 0, 0, 2, 0], ![1, 2, 2, 2, 0], ![0, 0, 1, 1, 0]],
    ![![0, 2, 2, 2, 0], ![1, 0, 0, 2, 0], ![1, 2, 0, 0, 0], ![0, 0, 2, 2, 0]],
    ![![2, 0, 2, 2, 0], ![1, 0, 0, 2, 0], ![1, 2, 0, 0, 0], ![1, 2, 2, 2, 0]],
    ![![1, 1, 0, 2, 1], ![1, 1, 0, 1, 0], ![1, 0, 0, 1, 2], ![1, 2, 0, 1, 2]],
    ![![0, 1, 1, 2, 0], ![2, 2, 1, 0, 0], ![0, 1, 0, 0, 0], ![1, 1, 1, 2, 0]],
    ![![2, 1, 0, 1, 0], ![2, 1, 1, 2, 0], ![0, 2, 0, 1, 0], ![0, 2, 0, 2, 0]],
    ![![2, 2, 0, 2, 0], ![2, 1, 1, 2, 0], ![0, 2, 0, 1, 0], ![0, 2, 0, 2, 0]],
    ![![0, 1, 0, 1, 2], ![2, 1, 0, 2, 2], ![0, 2, 0, 0, 0], ![1, 0, 0, 1, 2]],
    ![![0, 1, 1, 0, 0], ![1, 1, 1, 0, 1], ![1, 2, 1, 0, 0], ![1, 0, 1, 0, 0]],
    ![![2, 1, 0, 0, 0], ![1, 1, 0, 0, 1], ![2, 2, 2, 0, 0], ![2, 0, 2, 0, 0]],
    ![![0, 1, 0, 2, 1], ![2, 0, 0, 1, 0], ![1, 2, 0, 2, 1], ![0, 1, 0, 0, 0]],
    ![![0, 0, 0, 1, 2], ![2, 0, 0, 1, 0], ![1, 2, 0, 1, 2], ![0, 1, 0, 0, 0]],
    ![![1, 0, 2, 0, 0], ![2, 0, 0, 1, 0], ![2, 2, 2, 0, 0], ![1, 2, 1, 0, 0]],
    ![![2, 1, 1, 1, 0], ![2, 2, 2, 1, 0], ![2, 1, 2, 1, 0], ![2, 2, 0, 2, 0]],
    ![![1, 0, 1, 0, 0], ![1, 0, 2, 2, 0], ![1, 1, 2, 1, 0], ![0, 2, 0, 2, 0]],
    ![![1, 2, 1, 2, 0], ![1, 2, 2, 1, 0], ![1, 0, 2, 0, 0], ![0, 2, 0, 2, 0]],
    ![![1, 1, 2, 2, 0], ![2, 0, 0, 1, 0], ![0, 2, 2, 1, 0], ![1, 1, 0, 2, 0]],
    ![![1, 1, 2, 2, 0], ![2, 0, 0, 1, 0], ![1, 0, 2, 0, 0], ![1, 1, 0, 2, 0]],
    ![![1, 1, 2, 2, 0], ![2, 0, 0, 1, 0], ![1, 0, 2, 0, 0], ![0, 1, 1, 2, 0]],
    ![![2, 2, 2, 2, 0], ![1, 2, 0, 1, 0], ![2, 1, 2, 1, 0], ![1, 0, 0, 1, 0]],
    ![![1, 2, 2, 1, 0], ![2, 2, 0, 2, 0], ![2, 1, 2, 1, 0], ![2, 0, 0, 2, 0]],
    ![![0, 0, 2, 0, 1], ![0, 1, 0, 0, 2], ![1, 2, 2, 0, 1], ![2, 0, 1, 0, 1]],
    ![![0, 1, 2, 0, 0], ![2, 1, 2, 1, 0], ![2, 2, 0, 2, 0], ![1, 2, 0, 1, 0]],
    ![![1, 1, 0, 1, 0], ![0, 2, 2, 0, 0], ![2, 0, 2, 0, 0], ![2, 0, 0, 0, 0]],
    ![![2, 1, 0, 1, 0], ![2, 0, 2, 2, 0], ![2, 1, 2, 2, 0], ![1, 0, 0, 0, 0]],
    ![![1, 2, 2, 1, 0], ![1, 2, 0, 2, 0], ![2, 0, 0, 2, 0], ![2, 0, 0, 0, 0]],
    ![![0, 2, 2, 1, 0], ![1, 2, 0, 2, 0], ![1, 0, 0, 2, 0], ![1, 0, 0, 0, 0]],
    ![![1, 0, 1, 0, 0], ![1, 0, 2, 1, 0], ![2, 2, 1, 2, 0], ![0, 2, 1, 2, 0]],
    ![![2, 2, 2, 0, 2], ![2, 1, 1, 0, 2], ![0, 2, 1, 0, 2], ![2, 1, 2, 0, 1]],
    ![![0, 0, 1, 2, 0], ![2, 2, 0, 1, 0], ![1, 0, 0, 2, 0], ![2, 0, 0, 2, 0]],
    ![![1, 1, 2, 1, 0], ![0, 1, 2, 2, 0], ![1, 2, 2, 2, 0], ![0, 2, 2, 2, 0]],
    ![![1, 2, 0, 2, 0], ![0, 2, 0, 0, 0], ![1, 1, 1, 1, 0], ![0, 2, 2, 2, 0]],
    ![![2, 0, 1, 0, 0], ![1, 0, 1, 1, 0], ![1, 1, 1, 1, 0], ![2, 1, 1, 1, 0]],
    ![![2, 1, 1, 1, 0], ![0, 1, 1, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 1, 0, 0]],
    ![![2, 0, 0, 1, 1], ![2, 0, 0, 2, 0], ![2, 1, 0, 1, 0], ![0, 2, 0, 2, 0]],
    ![![0, 1, 2, 0, 1], ![1, 1, 2, 0, 0], ![1, 0, 2, 0, 0], ![2, 0, 2, 0, 0]],
    ![![1, 1, 2, 2, 0], ![0, 1, 2, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 1, 0, 0]],
    ![![1, 1, 0, 2, 0], ![0, 1, 0, 0, 0], ![1, 0, 2, 0, 0], ![0, 0, 1, 0, 0]],
    ![![0, 1, 1, 2, 0], ![2, 1, 1, 0, 0], ![1, 0, 2, 0, 0], ![2, 0, 2, 0, 0]],
    ![![1, 1, 1, 1, 0], ![0, 1, 2, 0, 0], ![1, 0, 1, 0, 0], ![0, 2, 2, 0, 0]],
    ![![1, 1, 1, 1, 0], ![0, 2, 0, 0, 0], ![1, 1, 2, 0, 0], ![0, 1, 1, 0, 0]],
    ![![1, 1, 1, 1, 0], ![2, 1, 1, 0, 0], ![2, 2, 1, 0, 0], ![2, 0, 2, 0, 0]],
    ![![1, 1, 1, 1, 0], ![1, 2, 2, 0, 0], ![0, 1, 0, 0, 0], ![0, 2, 1, 0, 0]],
    ![![0, 2, 1, 0, 0], ![1, 2, 1, 2, 0], ![1, 2, 0, 2, 0], ![2, 2, 0, 2, 0]],
    ![![0, 2, 1, 0, 0], ![2, 0, 0, 2, 0], ![2, 0, 1, 1, 0], ![0, 0, 2, 2, 0]],
    ![![0, 2, 2, 1, 0], ![2, 0, 1, 0, 0], ![2, 0, 2, 2, 0], ![0, 0, 2, 2, 0]],
    ![![0, 2, 1, 0, 0], ![2, 1, 2, 1, 0], ![2, 2, 2, 2, 0], ![1, 2, 2, 2, 0]],
    ![![1, 1, 0, 2, 0], ![1, 2, 0, 2, 0], ![2, 2, 2, 2, 0], ![2, 1, 1, 1, 0]],
    ![![1, 2, 0, 0, 2], ![0, 0, 2, 0, 1], ![1, 0, 1, 0, 1], ![2, 0, 1, 0, 1]],
    ![![0, 2, 1, 0, 0], ![1, 0, 2, 1, 0], ![0, 0, 2, 2, 0], ![1, 0, 0, 1, 0]],
    ![![1, 2, 1, 1, 0], ![2, 0, 2, 2, 0], ![1, 0, 2, 0, 0], ![2, 0, 0, 2, 0]],
    ![![0, 2, 2, 1, 0], ![1, 0, 0, 2, 0], ![1, 0, 2, 0, 0], ![0, 0, 2, 2, 0]],
    ![![2, 2, 2, 2, 0], ![2, 0, 0, 1, 0], ![2, 0, 2, 2, 0], ![1, 0, 2, 1, 0]],
    ![![2, 0, 0, 1, 1], ![1, 1, 0, 1, 2], ![1, 0, 0, 1, 0], ![2, 2, 0, 0, 1]],
    ![![0, 2, 2, 1, 0], ![0, 1, 2, 1, 0], ![1, 2, 1, 1, 0], ![0, 2, 1, 0, 0]],
    ![![2, 1, 2, 0, 2], ![2, 1, 0, 0, 1], ![0, 1, 1, 0, 2], ![0, 2, 1, 0, 0]],
    ![![0, 0, 1, 2, 0], ![1, 2, 1, 1, 0], ![0, 1, 2, 1, 0], ![0, 2, 1, 0, 0]],
    ![![0, 0, 1, 2, 0], ![1, 2, 1, 1, 0], ![0, 1, 1, 2, 0], ![0, 2, 1, 0, 0]]]

def cutCompatible : Fin 126 → Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  ![![![0, 2, 0, 1], ![0, 1, 0, 0], ![1, 2, 0, 1], ![0, 1, 2, 1]],
    ![![2, 1, 1, 0], ![1, 0, 1, 0], ![0, 2, 0, 0], ![2, 2, 1, 0]],
    ![![2, 0, 2, 0], ![2, 2, 2, 0], ![1, 2, 0, 0], ![1, 2, 1, 0]],
    ![![0, 1, 1, 0], ![1, 0, 1, 0], ![1, 0, 2, 0], ![1, 0, 0, 0]],
    ![![0, 0, 2, 0], ![1, 2, 2, 0], ![0, 0, 2, 0], ![0, 2, 1, 0]],
    ![![1, 1, 1, 0], ![0, 0, 1, 0], ![2, 0, 2, 0], ![2, 0, 0, 0]],
    ![![1, 1, 1, 0], ![0, 2, 2, 0], ![2, 0, 2, 0], ![1, 2, 0, 0]],
    ![![1, 1, 1, 0], ![2, 2, 1, 0], ![1, 2, 0, 0], ![2, 1, 0, 0]],
    ![![0, 0, 1, 0], ![2, 0, 2, 0], ![0, 2, 1, 0], ![1, 0, 1, 0]],
    ![![2, 0, 1, 0], ![2, 2, 1, 0], ![1, 0, 1, 0], ![1, 2, 0, 0]],
    ![![2, 0, 1, 0], ![0, 1, 1, 0], ![0, 1, 1, 0], ![1, 2, 0, 0]],
    ![![1, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 0], ![2, 1, 0, 0]],
    ![![2, 0, 0, 0], ![1, 0, 0, 0], ![1, 2, 0, 0], ![1, 0, 0, 0]],
    ![![1, 0, 0, 0], ![1, 2, 0, 0], ![1, 0, 0, 0], ![0, 2, 0, 0]],
    ![![1, 2, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 0], ![0, 1, 0, 0]],
    ![![2, 0, 0, 0], ![0, 1, 0, 0], ![2, 1, 0, 0], ![1, 2, 0, 0]],
    ![![2, 0, 0, 0], ![2, 2, 0, 0], ![0, 0, 0, 0], ![1, 2, 0, 0]],
    ![![0, 2, 0, 0], ![1, 0, 0, 0], ![1, 2, 0, 0], ![2, 1, 0, 0]],
    ![![1, 0, 0, 0], ![2, 2, 0, 0], ![0, 0, 0, 0], ![1, 2, 0, 0]],
    ![![2, 2, 0, 0], ![2, 2, 0, 0], ![2, 1, 0, 0], ![1, 2, 0, 0]],
    ![![1, 0, 0, 0], ![2, 2, 0, 0], ![1, 2, 0, 0], ![0, 0, 0, 0]],
    ![![2, 0, 1, 0], ![1, 0, 2, 0], ![0, 2, 2, 0], ![2, 0, 0, 0]],
    ![![2, 0, 2, 0], ![0, 0, 2, 0], ![0, 2, 2, 0], ![1, 0, 2, 0]],
    ![![0, 0, 0, 0], ![2, 0, 2, 0], ![0, 2, 0, 0], ![1, 0, 1, 0]],
    ![![0, 0, 2, 0], ![1, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 2, 0]],
    ![![0, 0, 2, 0], ![1, 0, 2, 0], ![0, 2, 1, 0], ![0, 0, 2, 0]],
    ![![2, 2, 0, 0], ![2, 2, 0, 0], ![1, 2, 0, 0], ![2, 2, 0, 0]],
    ![![1, 1, 0, 0], ![0, 2, 0, 0], ![1, 2, 0, 0], ![2, 0, 0, 0]],
    ![![2, 0, 0, 0], ![0, 1, 0, 0], ![0, 2, 0, 0], ![2, 2, 0, 0]],
    ![![1, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![2, 2, 0, 0]],
    ![![1, 0, 0, 0], ![1, 1, 0, 0], ![2, 2, 0, 0], ![2, 0, 0, 0]],
    ![![1, 1, 0, 0], ![2, 2, 0, 0], ![2, 0, 0, 0], ![0, 2, 0, 0]],
    ![![1, 1, 0, 0], ![2, 1, 0, 0], ![2, 1, 0, 0], ![0, 1, 0, 0]],
    ![![2, 1, 0, 0], ![0, 2, 0, 0], ![0, 0, 0, 0], ![2, 2, 0, 0]],
    ![![0, 2, 0, 0], ![0, 0, 0, 0], ![1, 2, 0, 0], ![2, 2, 0, 0]],
    ![![2, 2, 0, 0], ![0, 1, 0, 0], ![2, 0, 0, 0], ![0, 2, 0, 0]],
    ![![1, 1, 0, 0], ![0, 2, 0, 0], ![0, 2, 0, 0], ![2, 2, 0, 0]],
    ![![1, 2, 0, 0], ![0, 1, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0]],
    ![![2, 0, 0, 0], ![2, 0, 0, 0], ![0, 1, 0, 0], ![1, 2, 0, 0]],
    ![![0, 1, 0, 0], ![1, 0, 0, 0], ![1, 1, 0, 0], ![0, 2, 0, 0]],
    ![![0, 1, 0, 0], ![1, 2, 0, 0], ![2, 0, 0, 0], ![1, 2, 0, 0]],
    ![![0, 1, 0, 0], ![1, 2, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0]],
    ![![2, 0, 0, 0], ![1, 1, 0, 0], ![0, 2, 0, 0], ![1, 2, 0, 0]],
    ![![1, 0, 0, 0], ![0, 0, 0, 0], ![1, 2, 0, 0], ![1, 0, 0, 0]],
    ![![1, 0, 0, 0], ![2, 0, 0, 0], ![0, 2, 0, 0], ![1, 0, 0, 0]],
    ![![1, 0, 0, 0], ![2, 1, 0, 0], ![0, 1, 0, 0], ![1, 2, 0, 0]],
    ![![1, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]],
    ![![1, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]],
    ![![1, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]],
    ![![1, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0]],
    ![![2, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0]],
    ![![0, 0, 0, 0], ![2, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0]],
    ![![1, 0, 0, 0], ![2, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0]],
    ![![1, 0, 0, 0], ![2, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0], ![1, 0, 0, 0]],
    ![![1, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 1, 0], ![1, 0, 0, 0], ![2, 2, 1, 0], ![1, 0, 2, 0]],
    ![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 1, 0], ![2, 0, 1, 0]],
    ![![0, 0, 2, 0], ![0, 0, 0, 0], ![2, 2, 0, 0], ![0, 0, 1, 0]],
    ![![1, 0, 0, 0], ![1, 0, 2, 0], ![0, 2, 2, 0], ![2, 0, 1, 0]],
    ![![2, 0, 2, 0], ![2, 0, 1, 0], ![1, 2, 1, 0], ![2, 0, 1, 0]],
    ![![0, 2, 0, 0], ![0, 2, 0, 0], ![1, 1, 0, 0], ![0, 1, 0, 0]],
    ![![0, 1, 0, 0], ![0, 1, 0, 0], ![2, 0, 0, 0], ![0, 1, 0, 0]],
    ![![0, 2, 0, 0], ![2, 2, 0, 0], ![1, 1, 0, 0], ![0, 1, 0, 0]],
    ![![2, 2, 0, 0], ![1, 0, 0, 0], ![0, 2, 0, 0], ![2, 2, 0, 0]],
    ![![1, 1, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![2, 1, 0, 0]],
    ![![0, 2, 0, 0], ![2, 1, 0, 0], ![2, 2, 0, 0], ![1, 2, 0, 0]],
    ![![2, 1, 0, 0], ![2, 2, 0, 0], ![0, 1, 0, 0], ![2, 2, 0, 0]],
    ![![2, 0, 0, 0], ![1, 1, 0, 0], ![1, 2, 0, 0], ![2, 2, 0, 0]],
    ![![1, 2, 0, 0], ![1, 1, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0]],
    ![![1, 1, 0, 0], ![1, 1, 0, 0], ![0, 1, 0, 0], ![1, 2, 0, 0]],
    ![![2, 2, 0, 0], ![1, 2, 0, 0], ![0, 2, 0, 0], ![1, 2, 0, 0]],
    ![![2, 2, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![2, 1, 0, 0]],
    ![![1, 2, 0, 0], ![2, 2, 0, 0], ![0, 1, 0, 0], ![2, 2, 0, 0]],
    ![![2, 0, 0, 0], ![2, 2, 0, 0], ![0, 1, 0, 0], ![2, 2, 0, 0]],
    ![![2, 0, 0, 0], ![1, 1, 0, 0], ![1, 0, 0, 0], ![0, 2, 0, 0]],
    ![![2, 1, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0]],
    ![![2, 1, 0, 0], ![1, 2, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0]],
    ![![2, 1, 0, 0], ![2, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0]],
    ![![0, 2, 0, 0], ![2, 0, 0, 0], ![1, 1, 0, 0], ![2, 0, 0, 0]],
    ![![0, 1, 0, 0], ![2, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0]],
    ![![1, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0]],
    ![![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0]],
    ![![2, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0]],
    ![![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
    ![![1, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]],
    ![![1, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]],
    ![![2, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0]],
    ![![2, 0, 0, 0], ![2, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0]],
    ![![0, 2, 0, 0], ![2, 2, 0, 0], ![0, 0, 0, 0], ![0, 1, 0, 0]],
    ![![0, 1, 0, 0], ![2, 2, 0, 0], ![0, 2, 0, 0], ![0, 2, 0, 0]],
    ![![0, 1, 0, 0], ![2, 1, 0, 0], ![0, 0, 0, 0], ![0, 1, 0, 0]],
    ![![0, 2, 0, 0], ![2, 1, 0, 0], ![0, 1, 0, 0], ![0, 2, 0, 0]],
    ![![0, 0, 0, 0], ![2, 1, 0, 0], ![0, 2, 0, 0], ![0, 1, 0, 0]],
    ![![0, 0, 0, 0], ![2, 2, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, 0], ![2, 2, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 0, 0]],
    ![![0, 2, 0, 0], ![2, 2, 0, 0], ![0, 2, 0, 0], ![0, 1, 0, 0]],
    ![![2, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0]],
    ![![2, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0]],
    ![![1, 0, 0, 0], ![2, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0]],
    ![![0, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0]],
    ![![2, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0]],
    ![![1, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0]],
    ![![0, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0]],
    ![![0, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0], ![1, 0, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0]],
    ![![1, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]],
    ![![1, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]],
    ![![1, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0]],
    ![![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]

end AME96


/-! ## Inlined proof module: AME96.FastChecks -/


/-! Generated by scripts/generate_fast_checks.py. Each proof specializes the
finite data before invoking the kernel, avoiding repeated indexing of the big table. -/
namespace AME96
open Matrix
set_option maxHeartbeats 0
set_option maxRecDepth 65536

private theorem compatibleCase000 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 0) (cutOutside 0) d (cutCompatible 0 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 1, 2, 3] ![4, 5, 6, 7, 8] d
    ((![![0, 2, 0, 1], ![0, 1, 0, 0], ![1, 2, 0, 1], ![0, 1, 2, 1]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase001 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 1) (cutOutside 1) d (cutCompatible 1 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 1, 2, 4] ![3, 5, 6, 7, 8] d
    ((![![2, 1, 1, 0], ![1, 0, 1, 0], ![0, 2, 0, 0], ![2, 2, 1, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase002 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 2) (cutOutside 2) d (cutCompatible 2 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 1, 2, 5] ![3, 4, 6, 7, 8] d
    ((![![2, 0, 2, 0], ![2, 2, 2, 0], ![1, 2, 0, 0], ![1, 2, 1, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase003 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 3) (cutOutside 3) d (cutCompatible 3 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 1, 2, 6] ![3, 4, 5, 7, 8] d
    ((![![0, 1, 1, 0], ![1, 0, 1, 0], ![1, 0, 2, 0], ![1, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase004 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 4) (cutOutside 4) d (cutCompatible 4 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 1, 2, 7] ![3, 4, 5, 6, 8] d
    ((![![0, 0, 2, 0], ![1, 2, 2, 0], ![0, 0, 2, 0], ![0, 2, 1, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase005 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 5) (cutOutside 5) d (cutCompatible 5 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 1, 2, 8] ![3, 4, 5, 6, 7] d
    ((![![1, 1, 1, 0], ![0, 0, 1, 0], ![2, 0, 2, 0], ![2, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase006 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 6) (cutOutside 6) d (cutCompatible 6 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 1, 3, 4] ![2, 5, 6, 7, 8] d
    ((![![1, 1, 1, 0], ![0, 2, 2, 0], ![2, 0, 2, 0], ![1, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase007 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 7) (cutOutside 7) d (cutCompatible 7 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 1, 3, 5] ![2, 4, 6, 7, 8] d
    ((![![1, 1, 1, 0], ![2, 2, 1, 0], ![1, 2, 0, 0], ![2, 1, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase008 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 8) (cutOutside 8) d (cutCompatible 8 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 1, 3, 6] ![2, 4, 5, 7, 8] d
    ((![![0, 0, 1, 0], ![2, 0, 2, 0], ![0, 2, 1, 0], ![1, 0, 1, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase009 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 9) (cutOutside 9) d (cutCompatible 9 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 1, 3, 7] ![2, 4, 5, 6, 8] d
    ((![![2, 0, 1, 0], ![2, 2, 1, 0], ![1, 0, 1, 0], ![1, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase010 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 10) (cutOutside 10) d (cutCompatible 10 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 1, 3, 8] ![2, 4, 5, 6, 7] d
    ((![![2, 0, 1, 0], ![0, 1, 1, 0], ![0, 1, 1, 0], ![1, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase011 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 11) (cutOutside 11) d (cutCompatible 11 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 1, 4, 5] ![2, 3, 6, 7, 8] d
    ((![![1, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 0], ![2, 1, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase012 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 12) (cutOutside 12) d (cutCompatible 12 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 1, 4, 6] ![2, 3, 5, 7, 8] d
    ((![![2, 0, 0, 0], ![1, 0, 0, 0], ![1, 2, 0, 0], ![1, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase013 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 13) (cutOutside 13) d (cutCompatible 13 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 1, 4, 7] ![2, 3, 5, 6, 8] d
    ((![![1, 0, 0, 0], ![1, 2, 0, 0], ![1, 0, 0, 0], ![0, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase014 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 14) (cutOutside 14) d (cutCompatible 14 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 1, 4, 8] ![2, 3, 5, 6, 7] d
    ((![![1, 2, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 0], ![0, 1, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase015 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 15) (cutOutside 15) d (cutCompatible 15 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 1, 5, 6] ![2, 3, 4, 7, 8] d
    ((![![2, 0, 0, 0], ![0, 1, 0, 0], ![2, 1, 0, 0], ![1, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

#check compatibleCase015

private theorem compatibleCase016 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 16) (cutOutside 16) d (cutCompatible 16 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 1, 5, 7] ![2, 3, 4, 6, 8] d
    ((![![2, 0, 0, 0], ![2, 2, 0, 0], ![0, 0, 0, 0], ![1, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase017 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 17) (cutOutside 17) d (cutCompatible 17 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 1, 5, 8] ![2, 3, 4, 6, 7] d
    ((![![0, 2, 0, 0], ![1, 0, 0, 0], ![1, 2, 0, 0], ![2, 1, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase018 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 18) (cutOutside 18) d (cutCompatible 18 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 1, 6, 7] ![2, 3, 4, 5, 8] d
    ((![![1, 0, 0, 0], ![2, 2, 0, 0], ![0, 0, 0, 0], ![1, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase019 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 19) (cutOutside 19) d (cutCompatible 19 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 1, 6, 8] ![2, 3, 4, 5, 7] d
    ((![![2, 2, 0, 0], ![2, 2, 0, 0], ![2, 1, 0, 0], ![1, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase020 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 20) (cutOutside 20) d (cutCompatible 20 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 1, 7, 8] ![2, 3, 4, 5, 6] d
    ((![![1, 0, 0, 0], ![2, 2, 0, 0], ![1, 2, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase021 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 21) (cutOutside 21) d (cutCompatible 21 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 2, 3, 4] ![1, 5, 6, 7, 8] d
    ((![![2, 0, 1, 0], ![1, 0, 2, 0], ![0, 2, 2, 0], ![2, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase022 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 22) (cutOutside 22) d (cutCompatible 22 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 2, 3, 5] ![1, 4, 6, 7, 8] d
    ((![![2, 0, 2, 0], ![0, 0, 2, 0], ![0, 2, 2, 0], ![1, 0, 2, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase023 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 23) (cutOutside 23) d (cutCompatible 23 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 2, 3, 6] ![1, 4, 5, 7, 8] d
    ((![![0, 0, 0, 0], ![2, 0, 2, 0], ![0, 2, 0, 0], ![1, 0, 1, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase024 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 24) (cutOutside 24) d (cutCompatible 24 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 2, 3, 7] ![1, 4, 5, 6, 8] d
    ((![![0, 0, 2, 0], ![1, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 2, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase025 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 25) (cutOutside 25) d (cutCompatible 25 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 2, 3, 8] ![1, 4, 5, 6, 7] d
    ((![![0, 0, 2, 0], ![1, 0, 2, 0], ![0, 2, 1, 0], ![0, 0, 2, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase026 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 26) (cutOutside 26) d (cutCompatible 26 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 2, 4, 5] ![1, 3, 6, 7, 8] d
    ((![![2, 2, 0, 0], ![2, 2, 0, 0], ![1, 2, 0, 0], ![2, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase027 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 27) (cutOutside 27) d (cutCompatible 27 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 2, 4, 6] ![1, 3, 5, 7, 8] d
    ((![![1, 1, 0, 0], ![0, 2, 0, 0], ![1, 2, 0, 0], ![2, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase028 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 28) (cutOutside 28) d (cutCompatible 28 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 2, 4, 7] ![1, 3, 5, 6, 8] d
    ((![![2, 0, 0, 0], ![0, 1, 0, 0], ![0, 2, 0, 0], ![2, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase029 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 29) (cutOutside 29) d (cutCompatible 29 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 2, 4, 8] ![1, 3, 5, 6, 7] d
    ((![![1, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![2, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase030 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 30) (cutOutside 30) d (cutCompatible 30 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 2, 5, 6] ![1, 3, 4, 7, 8] d
    ((![![1, 0, 0, 0], ![1, 1, 0, 0], ![2, 2, 0, 0], ![2, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase031 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 31) (cutOutside 31) d (cutCompatible 31 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 2, 5, 7] ![1, 3, 4, 6, 8] d
    ((![![1, 1, 0, 0], ![2, 2, 0, 0], ![2, 0, 0, 0], ![0, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

#check compatibleCase031

private theorem compatibleCase032 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 32) (cutOutside 32) d (cutCompatible 32 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 2, 5, 8] ![1, 3, 4, 6, 7] d
    ((![![1, 1, 0, 0], ![2, 1, 0, 0], ![2, 1, 0, 0], ![0, 1, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase033 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 33) (cutOutside 33) d (cutCompatible 33 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 2, 6, 7] ![1, 3, 4, 5, 8] d
    ((![![2, 1, 0, 0], ![0, 2, 0, 0], ![0, 0, 0, 0], ![2, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase034 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 34) (cutOutside 34) d (cutCompatible 34 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 2, 6, 8] ![1, 3, 4, 5, 7] d
    ((![![0, 2, 0, 0], ![0, 0, 0, 0], ![1, 2, 0, 0], ![2, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase035 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 35) (cutOutside 35) d (cutCompatible 35 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 2, 7, 8] ![1, 3, 4, 5, 6] d
    ((![![2, 2, 0, 0], ![0, 1, 0, 0], ![2, 0, 0, 0], ![0, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase036 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 36) (cutOutside 36) d (cutCompatible 36 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 3, 4, 5] ![1, 2, 6, 7, 8] d
    ((![![1, 1, 0, 0], ![0, 2, 0, 0], ![0, 2, 0, 0], ![2, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase037 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 37) (cutOutside 37) d (cutCompatible 37 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 3, 4, 6] ![1, 2, 5, 7, 8] d
    ((![![1, 2, 0, 0], ![0, 1, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase038 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 38) (cutOutside 38) d (cutCompatible 38 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 3, 4, 7] ![1, 2, 5, 6, 8] d
    ((![![2, 0, 0, 0], ![2, 0, 0, 0], ![0, 1, 0, 0], ![1, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase039 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 39) (cutOutside 39) d (cutCompatible 39 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 3, 4, 8] ![1, 2, 5, 6, 7] d
    ((![![0, 1, 0, 0], ![1, 0, 0, 0], ![1, 1, 0, 0], ![0, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase040 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 40) (cutOutside 40) d (cutCompatible 40 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 3, 5, 6] ![1, 2, 4, 7, 8] d
    ((![![0, 1, 0, 0], ![1, 2, 0, 0], ![2, 0, 0, 0], ![1, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase041 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 41) (cutOutside 41) d (cutCompatible 41 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 3, 5, 7] ![1, 2, 4, 6, 8] d
    ((![![0, 1, 0, 0], ![1, 2, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase042 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 42) (cutOutside 42) d (cutCompatible 42 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 3, 5, 8] ![1, 2, 4, 6, 7] d
    ((![![2, 0, 0, 0], ![1, 1, 0, 0], ![0, 2, 0, 0], ![1, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase043 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 43) (cutOutside 43) d (cutCompatible 43 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 3, 6, 7] ![1, 2, 4, 5, 8] d
    ((![![1, 0, 0, 0], ![0, 0, 0, 0], ![1, 2, 0, 0], ![1, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase044 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 44) (cutOutside 44) d (cutCompatible 44 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 3, 6, 8] ![1, 2, 4, 5, 7] d
    ((![![1, 0, 0, 0], ![2, 0, 0, 0], ![0, 2, 0, 0], ![1, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase045 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 45) (cutOutside 45) d (cutCompatible 45 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 3, 7, 8] ![1, 2, 4, 5, 6] d
    ((![![1, 0, 0, 0], ![2, 1, 0, 0], ![0, 1, 0, 0], ![1, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase046 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 46) (cutOutside 46) d (cutCompatible 46 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 4, 5, 6] ![1, 2, 3, 7, 8] d
    ((![![1, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase047 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 47) (cutOutside 47) d (cutCompatible 47 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 4, 5, 7] ![1, 2, 3, 6, 8] d
    ((![![1, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

#check compatibleCase047

private theorem compatibleCase048 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 48) (cutOutside 48) d (cutCompatible 48 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 4, 5, 8] ![1, 2, 3, 6, 7] d
    ((![![1, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase049 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 49) (cutOutside 49) d (cutCompatible 49 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 4, 6, 7] ![1, 2, 3, 5, 8] d
    ((![![1, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase050 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 50) (cutOutside 50) d (cutCompatible 50 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 4, 6, 8] ![1, 2, 3, 5, 7] d
    ((![![2, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase051 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 51) (cutOutside 51) d (cutCompatible 51 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 4, 7, 8] ![1, 2, 3, 5, 6] d
    ((![![0, 0, 0, 0], ![2, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase052 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 52) (cutOutside 52) d (cutCompatible 52 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 5, 6, 7] ![1, 2, 3, 4, 8] d
    ((![![1, 0, 0, 0], ![2, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase053 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 53) (cutOutside 53) d (cutCompatible 53 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 5, 6, 8] ![1, 2, 3, 4, 7] d
    ((![![1, 0, 0, 0], ![2, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase054 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 54) (cutOutside 54) d (cutCompatible 54 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 5, 7, 8] ![1, 2, 3, 4, 6] d
    ((![![0, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0], ![1, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase055 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 55) (cutOutside 55) d (cutCompatible 55 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![0, 6, 7, 8] ![1, 2, 3, 4, 5] d
    ((![![1, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase056 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 56) (cutOutside 56) d (cutCompatible 56 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 2, 3, 4] ![0, 5, 6, 7, 8] d
    ((![![0, 0, 1, 0], ![1, 0, 0, 0], ![2, 2, 1, 0], ![1, 0, 2, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase057 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 57) (cutOutside 57) d (cutCompatible 57 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 2, 3, 5] ![0, 4, 6, 7, 8] d
    ((![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 1, 0], ![2, 0, 1, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase058 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 58) (cutOutside 58) d (cutCompatible 58 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 2, 3, 6] ![0, 4, 5, 7, 8] d
    ((![![0, 0, 2, 0], ![0, 0, 0, 0], ![2, 2, 0, 0], ![0, 0, 1, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase059 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 59) (cutOutside 59) d (cutCompatible 59 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 2, 3, 7] ![0, 4, 5, 6, 8] d
    ((![![1, 0, 0, 0], ![1, 0, 2, 0], ![0, 2, 2, 0], ![2, 0, 1, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase060 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 60) (cutOutside 60) d (cutCompatible 60 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 2, 3, 8] ![0, 4, 5, 6, 7] d
    ((![![2, 0, 2, 0], ![2, 0, 1, 0], ![1, 2, 1, 0], ![2, 0, 1, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase061 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 61) (cutOutside 61) d (cutCompatible 61 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 2, 4, 5] ![0, 3, 6, 7, 8] d
    ((![![0, 2, 0, 0], ![0, 2, 0, 0], ![1, 1, 0, 0], ![0, 1, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase062 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 62) (cutOutside 62) d (cutCompatible 62 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 2, 4, 6] ![0, 3, 5, 7, 8] d
    ((![![0, 1, 0, 0], ![0, 1, 0, 0], ![2, 0, 0, 0], ![0, 1, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase063 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 63) (cutOutside 63) d (cutCompatible 63 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 2, 4, 7] ![0, 3, 5, 6, 8] d
    ((![![0, 2, 0, 0], ![2, 2, 0, 0], ![1, 1, 0, 0], ![0, 1, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

#check compatibleCase063

private theorem compatibleCase064 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 64) (cutOutside 64) d (cutCompatible 64 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 2, 4, 8] ![0, 3, 5, 6, 7] d
    ((![![2, 2, 0, 0], ![1, 0, 0, 0], ![0, 2, 0, 0], ![2, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase065 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 65) (cutOutside 65) d (cutCompatible 65 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 2, 5, 6] ![0, 3, 4, 7, 8] d
    ((![![1, 1, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![2, 1, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase066 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 66) (cutOutside 66) d (cutCompatible 66 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 2, 5, 7] ![0, 3, 4, 6, 8] d
    ((![![0, 2, 0, 0], ![2, 1, 0, 0], ![2, 2, 0, 0], ![1, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase067 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 67) (cutOutside 67) d (cutCompatible 67 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 2, 5, 8] ![0, 3, 4, 6, 7] d
    ((![![2, 1, 0, 0], ![2, 2, 0, 0], ![0, 1, 0, 0], ![2, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase068 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 68) (cutOutside 68) d (cutCompatible 68 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 2, 6, 7] ![0, 3, 4, 5, 8] d
    ((![![2, 0, 0, 0], ![1, 1, 0, 0], ![1, 2, 0, 0], ![2, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase069 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 69) (cutOutside 69) d (cutCompatible 69 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 2, 6, 8] ![0, 3, 4, 5, 7] d
    ((![![1, 2, 0, 0], ![1, 1, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase070 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 70) (cutOutside 70) d (cutCompatible 70 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 2, 7, 8] ![0, 3, 4, 5, 6] d
    ((![![1, 1, 0, 0], ![1, 1, 0, 0], ![0, 1, 0, 0], ![1, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase071 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 71) (cutOutside 71) d (cutCompatible 71 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 3, 4, 5] ![0, 2, 6, 7, 8] d
    ((![![2, 2, 0, 0], ![1, 2, 0, 0], ![0, 2, 0, 0], ![1, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase072 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 72) (cutOutside 72) d (cutCompatible 72 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 3, 4, 6] ![0, 2, 5, 7, 8] d
    ((![![2, 2, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![2, 1, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase073 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 73) (cutOutside 73) d (cutCompatible 73 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 3, 4, 7] ![0, 2, 5, 6, 8] d
    ((![![1, 2, 0, 0], ![2, 2, 0, 0], ![0, 1, 0, 0], ![2, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase074 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 74) (cutOutside 74) d (cutCompatible 74 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 3, 4, 8] ![0, 2, 5, 6, 7] d
    ((![![2, 0, 0, 0], ![2, 2, 0, 0], ![0, 1, 0, 0], ![2, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase075 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 75) (cutOutside 75) d (cutCompatible 75 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 3, 5, 6] ![0, 2, 4, 7, 8] d
    ((![![2, 0, 0, 0], ![1, 1, 0, 0], ![1, 0, 0, 0], ![0, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase076 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 76) (cutOutside 76) d (cutCompatible 76 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 3, 5, 7] ![0, 2, 4, 6, 8] d
    ((![![2, 1, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase077 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 77) (cutOutside 77) d (cutCompatible 77 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 3, 5, 8] ![0, 2, 4, 6, 7] d
    ((![![2, 1, 0, 0], ![1, 2, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase078 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 78) (cutOutside 78) d (cutCompatible 78 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 3, 6, 7] ![0, 2, 4, 5, 8] d
    ((![![2, 1, 0, 0], ![2, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase079 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 79) (cutOutside 79) d (cutCompatible 79 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 3, 6, 8] ![0, 2, 4, 5, 7] d
    ((![![0, 2, 0, 0], ![2, 0, 0, 0], ![1, 1, 0, 0], ![2, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

#check compatibleCase079

private theorem compatibleCase080 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 80) (cutOutside 80) d (cutCompatible 80 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 3, 7, 8] ![0, 2, 4, 5, 6] d
    ((![![0, 1, 0, 0], ![2, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase081 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 81) (cutOutside 81) d (cutCompatible 81 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 4, 5, 6] ![0, 2, 3, 7, 8] d
    ((![![1, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase082 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 82) (cutOutside 82) d (cutCompatible 82 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 4, 5, 7] ![0, 2, 3, 6, 8] d
    ((![![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase083 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 83) (cutOutside 83) d (cutCompatible 83 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 4, 5, 8] ![0, 2, 3, 6, 7] d
    ((![![2, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase084 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 84) (cutOutside 84) d (cutCompatible 84 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 4, 6, 7] ![0, 2, 3, 5, 8] d
    ((![![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase085 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 85) (cutOutside 85) d (cutCompatible 85 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 4, 6, 8] ![0, 2, 3, 5, 7] d
    ((![![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase086 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 86) (cutOutside 86) d (cutCompatible 86 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 4, 7, 8] ![0, 2, 3, 5, 6] d
    ((![![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase087 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 87) (cutOutside 87) d (cutCompatible 87 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 5, 6, 7] ![0, 2, 3, 4, 8] d
    ((![![1, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase088 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 88) (cutOutside 88) d (cutCompatible 88 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 5, 6, 8] ![0, 2, 3, 4, 7] d
    ((![![1, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase089 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 89) (cutOutside 89) d (cutCompatible 89 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 5, 7, 8] ![0, 2, 3, 4, 6] d
    ((![![2, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase090 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 90) (cutOutside 90) d (cutCompatible 90 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![1, 6, 7, 8] ![0, 2, 3, 4, 5] d
    ((![![2, 0, 0, 0], ![2, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase091 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 91) (cutOutside 91) d (cutCompatible 91 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![2, 3, 4, 5] ![0, 1, 6, 7, 8] d
    ((![![0, 2, 0, 0], ![2, 2, 0, 0], ![0, 0, 0, 0], ![0, 1, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase092 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 92) (cutOutside 92) d (cutCompatible 92 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![2, 3, 4, 6] ![0, 1, 5, 7, 8] d
    ((![![0, 1, 0, 0], ![2, 2, 0, 0], ![0, 2, 0, 0], ![0, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase093 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 93) (cutOutside 93) d (cutCompatible 93 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![2, 3, 4, 7] ![0, 1, 5, 6, 8] d
    ((![![0, 1, 0, 0], ![2, 1, 0, 0], ![0, 0, 0, 0], ![0, 1, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase094 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 94) (cutOutside 94) d (cutCompatible 94 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![2, 3, 4, 8] ![0, 1, 5, 6, 7] d
    ((![![0, 2, 0, 0], ![2, 1, 0, 0], ![0, 1, 0, 0], ![0, 2, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase095 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 95) (cutOutside 95) d (cutCompatible 95 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![2, 3, 5, 6] ![0, 1, 4, 7, 8] d
    ((![![0, 0, 0, 0], ![2, 1, 0, 0], ![0, 2, 0, 0], ![0, 1, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

#check compatibleCase095

private theorem compatibleCase096 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 96) (cutOutside 96) d (cutCompatible 96 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![2, 3, 5, 7] ![0, 1, 4, 6, 8] d
    ((![![0, 0, 0, 0], ![2, 2, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase097 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 97) (cutOutside 97) d (cutCompatible 97 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![2, 3, 5, 8] ![0, 1, 4, 6, 7] d
    ((![![0, 0, 0, 0], ![2, 2, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase098 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 98) (cutOutside 98) d (cutCompatible 98 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![2, 3, 6, 7] ![0, 1, 4, 5, 8] d
    ((![![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase099 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 99) (cutOutside 99) d (cutCompatible 99 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![2, 3, 6, 8] ![0, 1, 4, 5, 7] d
    ((![![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase100 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 100) (cutOutside 100) d (cutCompatible 100 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![2, 3, 7, 8] ![0, 1, 4, 5, 6] d
    ((![![0, 2, 0, 0], ![2, 2, 0, 0], ![0, 2, 0, 0], ![0, 1, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase101 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 101) (cutOutside 101) d (cutCompatible 101 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![2, 4, 5, 6] ![0, 1, 3, 7, 8] d
    ((![![2, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase102 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 102) (cutOutside 102) d (cutCompatible 102 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![2, 4, 5, 7] ![0, 1, 3, 6, 8] d
    ((![![2, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase103 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 103) (cutOutside 103) d (cutCompatible 103 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![2, 4, 5, 8] ![0, 1, 3, 6, 7] d
    ((![![1, 0, 0, 0], ![2, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase104 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 104) (cutOutside 104) d (cutCompatible 104 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![2, 4, 6, 7] ![0, 1, 3, 5, 8] d
    ((![![0, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase105 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 105) (cutOutside 105) d (cutCompatible 105 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![2, 4, 6, 8] ![0, 1, 3, 5, 7] d
    ((![![2, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase106 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 106) (cutOutside 106) d (cutCompatible 106 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![2, 4, 7, 8] ![0, 1, 3, 5, 6] d
    ((![![1, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase107 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 107) (cutOutside 107) d (cutCompatible 107 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![2, 5, 6, 7] ![0, 1, 3, 4, 8] d
    ((![![0, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase108 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 108) (cutOutside 108) d (cutCompatible 108 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![2, 5, 6, 8] ![0, 1, 3, 4, 7] d
    ((![![0, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase109 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 109) (cutOutside 109) d (cutCompatible 109 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![2, 5, 7, 8] ![0, 1, 3, 4, 6] d
    ((![![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase110 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 110) (cutOutside 110) d (cutCompatible 110 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![2, 6, 7, 8] ![0, 1, 3, 4, 5] d
    ((![![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase111 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 111) (cutOutside 111) d (cutCompatible 111 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![3, 4, 5, 6] ![0, 1, 2, 7, 8] d
    ((![![0, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0], ![1, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

#check compatibleCase111

private theorem compatibleCase112 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 112) (cutOutside 112) d (cutCompatible 112 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![3, 4, 5, 7] ![0, 1, 2, 6, 8] d
    ((![![0, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase113 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 113) (cutOutside 113) d (cutCompatible 113 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![3, 4, 5, 8] ![0, 1, 2, 6, 7] d
    ((![![1, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase114 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 114) (cutOutside 114) d (cutCompatible 114 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![3, 4, 6, 7] ![0, 1, 2, 5, 8] d
    ((![![0, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase115 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 115) (cutOutside 115) d (cutCompatible 115 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![3, 4, 6, 8] ![0, 1, 2, 5, 7] d
    ((![![0, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase116 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 116) (cutOutside 116) d (cutCompatible 116 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![3, 4, 7, 8] ![0, 1, 2, 5, 6] d
    ((![![1, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase117 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 117) (cutOutside 117) d (cutCompatible 117 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![3, 5, 6, 7] ![0, 1, 2, 4, 8] d
    ((![![0, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase118 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 118) (cutOutside 118) d (cutCompatible 118 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![3, 5, 6, 8] ![0, 1, 2, 4, 7] d
    ((![![0, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase119 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 119) (cutOutside 119) d (cutCompatible 119 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![3, 5, 7, 8] ![0, 1, 2, 4, 6] d
    ((![![1, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase120 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 120) (cutOutside 120) d (cutCompatible 120 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![3, 6, 7, 8] ![0, 1, 2, 4, 5] d
    ((![![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase121 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 121) (cutOutside 121) d (cutCompatible 121 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![4, 5, 6, 7] ![0, 1, 2, 3, 8] d
    ((![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase122 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 122) (cutOutside 122) d (cutCompatible 122 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![4, 5, 6, 8] ![0, 1, 2, 3, 7] d
    ((![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase123 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 123) (cutOutside 123) d (cutCompatible 123 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![4, 5, 7, 8] ![0, 1, 2, 3, 6] d
    ((![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase124 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 124) (cutOutside 124) d (cutCompatible 124 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![4, 6, 7, 8] ![0, 1, 2, 3, 5] d
    ((![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

private theorem compatibleCase125 : ∀ d : Difference, d ≠ 0 →
    Cancels (cutSelected 125) (cutOutside 125) d (cutCompatible 125 *ᵥ d) := by
  change ∀ d : Difference, d ≠ 0 → Cancels ![5, 6, 7, 8] ![0, 1, 2, 3, 4] d
    ((![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ d)
  decide +kernel

theorem fastCompatible_cancels : ∀ (k : Fin 126) (d : Difference),
    d ≠ 0 → Cancels (cutSelected k) (cutOutside k) d (cutCompatible k *ᵥ d) := by
  intro k
  fin_cases k
  · exact compatibleCase000
  · exact compatibleCase001
  · exact compatibleCase002
  · exact compatibleCase003
  · exact compatibleCase004
  · exact compatibleCase005
  · exact compatibleCase006
  · exact compatibleCase007
  · exact compatibleCase008
  · exact compatibleCase009
  · exact compatibleCase010
  · exact compatibleCase011
  · exact compatibleCase012
  · exact compatibleCase013
  · exact compatibleCase014
  · exact compatibleCase015
  · exact compatibleCase016
  · exact compatibleCase017
  · exact compatibleCase018
  · exact compatibleCase019
  · exact compatibleCase020
  · exact compatibleCase021
  · exact compatibleCase022
  · exact compatibleCase023
  · exact compatibleCase024
  · exact compatibleCase025
  · exact compatibleCase026
  · exact compatibleCase027
  · exact compatibleCase028
  · exact compatibleCase029
  · exact compatibleCase030
  · exact compatibleCase031
  · exact compatibleCase032
  · exact compatibleCase033
  · exact compatibleCase034
  · exact compatibleCase035
  · exact compatibleCase036
  · exact compatibleCase037
  · exact compatibleCase038
  · exact compatibleCase039
  · exact compatibleCase040
  · exact compatibleCase041
  · exact compatibleCase042
  · exact compatibleCase043
  · exact compatibleCase044
  · exact compatibleCase045
  · exact compatibleCase046
  · exact compatibleCase047
  · exact compatibleCase048
  · exact compatibleCase049
  · exact compatibleCase050
  · exact compatibleCase051
  · exact compatibleCase052
  · exact compatibleCase053
  · exact compatibleCase054
  · exact compatibleCase055
  · exact compatibleCase056
  · exact compatibleCase057
  · exact compatibleCase058
  · exact compatibleCase059
  · exact compatibleCase060
  · exact compatibleCase061
  · exact compatibleCase062
  · exact compatibleCase063
  · exact compatibleCase064
  · exact compatibleCase065
  · exact compatibleCase066
  · exact compatibleCase067
  · exact compatibleCase068
  · exact compatibleCase069
  · exact compatibleCase070
  · exact compatibleCase071
  · exact compatibleCase072
  · exact compatibleCase073
  · exact compatibleCase074
  · exact compatibleCase075
  · exact compatibleCase076
  · exact compatibleCase077
  · exact compatibleCase078
  · exact compatibleCase079
  · exact compatibleCase080
  · exact compatibleCase081
  · exact compatibleCase082
  · exact compatibleCase083
  · exact compatibleCase084
  · exact compatibleCase085
  · exact compatibleCase086
  · exact compatibleCase087
  · exact compatibleCase088
  · exact compatibleCase089
  · exact compatibleCase090
  · exact compatibleCase091
  · exact compatibleCase092
  · exact compatibleCase093
  · exact compatibleCase094
  · exact compatibleCase095
  · exact compatibleCase096
  · exact compatibleCase097
  · exact compatibleCase098
  · exact compatibleCase099
  · exact compatibleCase100
  · exact compatibleCase101
  · exact compatibleCase102
  · exact compatibleCase103
  · exact compatibleCase104
  · exact compatibleCase105
  · exact compatibleCase106
  · exact compatibleCase107
  · exact compatibleCase108
  · exact compatibleCase109
  · exact compatibleCase110
  · exact compatibleCase111
  · exact compatibleCase112
  · exact compatibleCase113
  · exact compatibleCase114
  · exact compatibleCase115
  · exact compatibleCase116
  · exact compatibleCase117
  · exact compatibleCase118
  · exact compatibleCase119
  · exact compatibleCase120
  · exact compatibleCase121
  · exact compatibleCase122
  · exact compatibleCase123
  · exact compatibleCase124
  · exact compatibleCase125

end AME96

#print axioms AME96.fastCompatible_cancels


/-! ## Inlined proof module: AME96.CutMatrices -/


namespace AME96
open Matrix
open scoped BigOperators
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem leftInverse_entries : ∀ (k : Fin 126) (i j : Fin 4),
    (cutLeftInverse k * cBlock (cutSelected k) (cutOutside k)) i j =
      (1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) i j := by
  change ∀ (k : Fin 126) (i j : Fin 4),
    (∑ u : Fin 5, cutLeftInverse k i u * C (cutOutside k u) (cutSelected k j) : ZMod 3) =
      if i = j then 1 else 0
  decide +kernel

private theorem compatible_entries : ∀ (k : Fin 126) (i j : Fin 4),
    (cutLeftInverse k * tBlock (cutSelected k) (cutOutside k)) i j =
      (-cutCompatible k) i j := by
  change ∀ (k : Fin 126) (i j : Fin 4),
    (∑ u : Fin 5, cutLeftInverse k i u * B (cutSelected k j) (cutOutside k u) : ZMod 3) =
      -(cutCompatible k i j)
  decide +kernel

theorem cutLeftInverse_valid (k : Fin 126) :
    cutLeftInverse k * cBlock (cutSelected k) (cutOutside k) = 1 :=
  funext fun i => funext fun j => leftInverse_entries k i j

theorem cutCompatible_valid (k : Fin 126) :
    cutLeftInverse k * tBlock (cutSelected k) (cutOutside k) = -cutCompatible k :=
  funext fun i => funext fun j => compatible_entries k i j

end AME96


/-! ## Inlined proof module: AME96.CutCoverage -/


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


/-! ## Inlined proof module: AME96.AllCuts -/


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


/-! ## Inlined proof module: AME96.FCInterface -/


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


/-! ## Inlined proof module: AME96.State -/


/-! The supplied AME(9,6) candidate as a normalized state in the exact FC interface. -/
namespace AME96
open OpenQuantumProblem35
open scoped BigOperators

def localSixEquiv : Fin 2 × Fin 3 ≃ Fin 6 := finProdFinEquiv

theorem localSixEquiv_val (x : Fin 2) (y : Fin 3) :
    (localSixEquiv (x, y)).val = 3 * x.val + y.val := by
  change y.val + 3 * x.val = 3 * x.val + y.val
  omega

def bits (z : Config 9 6) (i : Fin 9) : ZMod 2 :=
  ((localSixEquiv.symm (z i)).1.val : ZMod 2)

def trits (z : Config 9 6) (i : Fin 9) : ZMod 3 :=
  ((localSixEquiv.symm (z i)).2.val : ZMod 3)

def liftedBits (z : Config 9 6) (i : Fin 9) : ZMod 3 :=
  ((localSixEquiv.symm (z i)).1.val : ZMod 3)

def ternaryPhase (z : Config 9 6) : ZMod 3 :=
  quadratic C (trits z) +
    (∑ i, ∑ j, liftedBits z i * B i j * trits z j) +
    quadratic H (liftedBits z)

noncomputable def coefficient : ℂ := (Real.sqrt ((6 : ℝ) ^ 9))⁻¹

/-- The supplied full-support phase state, with local label 3x+y. -/
noncomputable def amplitude (z : Config 9 6) : ℂ :=
  coefficient * ZMod.stdAddChar (quadratic G (bits z)) *
    ZMod.stdAddChar (ternaryPhase z)

noncomputable def state : StateVector 9 6 := mkStateVector amplitude

theorem amplitude_norm_sq (z : Config 9 6) : ‖amplitude z‖ ^ 2 = ((6 : ℝ) ^ 9)⁻¹ := by
  simp only [amplitude, norm_mul, character_norm, mul_one]
  simp only [coefficient, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow]
  rw [Real.sq_sqrt (by positivity)]

/-- Normalization of the actual FC state; this does not yet prove its AME property. -/
theorem state_normalized : IsNormalized state := by
  apply (isNormalized_iff_norm_sq_eq_one state).mpr
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ z : Config 9 6, ‖amplitude z‖ ^ 2) = 1
  simp only [amplitude_norm_sq, Finset.sum_const, Finset.card_univ,
    card_config, nsmul_eq_mul]
  norm_num

end AME96


/-! ## Inlined proof module: AME96.Reduction -/


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


/-! ## Inlined proof module: AME96.Existence -/


/-! The finite table controls arbitrary orderings of both sides of a partition. -/
namespace AME96
open scoped BigOperators

noncomputable def checkedPartition (k : Fin 126) : Partition :=
  Equiv.ofBijective (Sum.elim (cutSelected k) (cutOutside k)) (allCuts_partition k)

@[simp] theorem checkedPartition_left (k : Fin 126) (i : Fin 4) :
    checkedPartition k (.inl i) = cutSelected k i := rfl

@[simp] theorem checkedPartition_right (k : Fin 126) (i : Fin 5) :
    checkedPartition k (.inr i) = cutOutside k i := rfl

private theorem reorder {α β : Type*} (f g : α → β)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hrange : Set.range f = Set.range g) :
    ∃ a : Equiv.Perm α, ∀ i, f i = g (a i) := by
  let a := (Equiv.ofInjective f hf).trans
    ((Set.equivOfEq hrange).trans (Equiv.ofInjective g hg).symm)
  refine ⟨a, ?_⟩
  intro i
  have h := (Equiv.ofInjective g hg).apply_symm_apply
    ((Set.equivOfEq hrange) ((Equiv.ofInjective f hf) i))
  exact (congrArg Subtype.val h).symm

theorem cancels_reorder (s s₀ : Selected) (o o₀ : Outside)
    (a : Equiv.Perm (Fin 4)) (hs : ∀ j, s j = s₀ (a j))
    (ho : ∀ i, ∃ j, o j = o₀ i) (d e : Difference)
    (h : Cancels s₀ o₀ (d ∘ a.symm) (e ∘ a.symm)) : Cancels s o d e := by
  have ha (i j) (hij : o j = o₀ i) :
      alpha s o d e j = alpha s₀ o₀ (d ∘ a.symm) (e ∘ a.symm) i := by
    unfold alpha
    calc
      _ = ∑ k, (C (o₀ i) (s₀ (a k)) * (e ∘ a.symm) (a k) +
          B (s₀ (a k)) (o₀ i) * (d ∘ a.symm) (a k)) := by simp [hs, hij]
      _ = _ := Equiv.sum_comp a (fun k => C (o₀ i) (s₀ k) * (e ∘ a.symm) k + B (s₀ k) (o₀ i) * (d ∘ a.symm) k)
  have hb (i j) (hij : o j = o₀ i) :
      beta s o d e j = beta s₀ o₀ (d ∘ a.symm) (e ∘ a.symm) i := by
    unfold beta
    calc
      _ = ∑ k, (B (o₀ i) (s₀ (a k)) * (e ∘ a.symm) (a k) +
          H (o₀ i) (s₀ (a k)) * (d ∘ a.symm) (a k)) := by simp [hs, hij]
      _ = _ := Equiv.sum_comp a (fun k => B (o₀ i) (s₀ k) * (e ∘ a.symm) k + H (o₀ i) (s₀ k) * (d ∘ a.symm) k)
  have hr (i j) (hij : o j = o₀ i) :
      binaryCoeff s o d j = binaryCoeff s₀ o₀ (d ∘ a.symm) i := by
    unfold binaryCoeff
    calc
      _ = ∑ k, G (o₀ i) (s₀ (a k)) *
          (if (d ∘ a.symm) (a k) = 0 then 0 else 1) := by simp [hs, hij]
      _ = _ := Equiv.sum_comp a (fun k => G (o₀ i) (s₀ k) * (if (d ∘ a.symm) k = 0 then 0 else 1))
  rcases h with ⟨i, hi⟩ | ⟨i, hi, hi'⟩
  · obtain ⟨j, hj⟩ := ho i
    exact Or.inl ⟨j, by rwa [ha i j hj]⟩
  · obtain ⟨j, hj⟩ := ho i
    exact Or.inr ⟨j, by rwa [hr i j hj], by rwa [hb i j hj]⟩

/-- Covers every partition, including every ordering used by FC's permutation quantifier. -/
theorem everyPartition_cancels (p : Partition) (d e : Difference)
    (hde : d ≠ 0 ∨ e ≠ 0) : Cancels (select p) (outside p) d e := by
  have hs : Function.Injective (select p) := p.injective.comp Sum.inl_injective
  let S := Finset.univ.image (select p)
  have hcard : S.card = 4 := by
    rw [Finset.card_image_of_injective _ hs]
    rfl
  obtain ⟨k, hk⟩ := allCuts_complete S hcard
  let q := checkedPartition k
  have hq : Function.Injective (cutSelected k) := by
    exact q.injective.comp Sum.inl_injective
  have hrange : Set.range (select p) = Set.range (cutSelected k) := by
    ext i
    have hi := Finset.ext_iff.mp hk i
    simpa [S] using hi.symm
  obtain ⟨a, ha⟩ := reorder (select p) (cutSelected k) hs hq hrange
  have ho : ∀ i, ∃ j, outside p j = cutOutside k i := by
    intro i
    obtain ⟨t, ht⟩ := p.surjective (cutOutside k i)
    cases t with
    | inr j => exact ⟨j, ht⟩
    | inl j =>
        have hj : cutOutside k i ∈ Set.range (select p) := ⟨j, ht⟩
        rw [hrange] at hj
        obtain ⟨j', hj'⟩ := hj
        have heq : q (.inl j') = q (.inr i) := hj'
        have hfalse := q.injective heq
        cases hfalse
  apply cancels_reorder _ _ _ _ a ha ho
  apply allCuts_cancels
  rcases hde with hd | he
  · left
    intro h
    apply hd
    funext j
    simpa using congrFun h (a j)
  · right
    intro h
    apply he
    funext j
    simpa using congrFun h (a j)

end AME96


namespace AME96
open OpenQuantumProblem35

/-- The supplied state is AME for every permutation in the pinned FC definition. -/
theorem state_isAME : IsAME state :=
  state_isAME_of_cancellation (fun p d e h => everyPartition_cancels p d e h)

/-- Unconditional solution of the pinned FC proposition `ExistsAME 9 6`. -/
theorem exists_ame_9_6 : ExistsAME 9 6 := ⟨state, state_isAME⟩

end AME96

#print axioms AME96.exists_ame_9_6


/-! ## Inlined proof module: AME96.FormalTarget -/


/-!
The exact proposition appearing on the right of the pinned Formal Conjectures
`OpenQuantumProblem35.ame_9_6_open` declaration is `ExistsAME 9 6`.
Filling its answer with `True` gives the following target, proved from the
explicit state without using the open declaration.
-/

namespace AME96
open OpenQuantumProblem35

theorem ame_9_6_answer_true : answer(True) ↔ ExistsAME 9 6 := by
  constructor
  · intro _
    exact exists_ame_9_6
  · intro _
    trivial

end AME96


#check AME96.exists_ame_9_6
#check AME96.ame_9_6_answer_true
#print axioms AME96.exists_ame_9_6
#print axioms AME96.ame_9_6_answer_true
