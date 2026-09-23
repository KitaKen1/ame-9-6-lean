import AME96.Finite
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

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
