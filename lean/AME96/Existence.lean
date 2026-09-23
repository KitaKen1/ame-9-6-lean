import AME96.Reduction
import AME96.AllCuts

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
    ((Equiv.setCongr hrange).trans (Equiv.ofInjective g hg).symm)
  refine ⟨a, ?_⟩
  intro i
  have h := (Equiv.ofInjective g hg).apply_symm_apply
    ((Equiv.setCongr hrange) ((Equiv.ofInjective f hf) i))
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
