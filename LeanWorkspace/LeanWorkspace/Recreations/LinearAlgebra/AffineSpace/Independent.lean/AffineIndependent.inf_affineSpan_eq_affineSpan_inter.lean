import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

theorem AffineIndependent.inf_affineSpan_eq_affineSpan_inter [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) (s₁ s₂ : Set ι) :
    affineSpan k (p '' s₁) ⊓ affineSpan k (p '' s₂) = affineSpan k (p '' (s₁ ∩ s₂)) := by
  classical
  ext p'
  simp_rw [AffineSubspace.mem_inf_iff, Set.image_eq_range, mem_affineSpan_iff_eq_affineCombination,
    ← Finset.eq_affineCombination_subset_iff_eq_affineCombination_subtype]
  constructor
  · rintro ⟨⟨fs₁, hfs₁, w₁, hw₁, rfl⟩, ⟨fs₂, hfs₂, w₂, hw₂, hw₁₂⟩⟩
    rw [affineIndependent_iff_indicator_eq_of_affineCombination_eq] at ha
    replace ha := ha fs₁ fs₂ w₁ w₂ hw₁ hw₂ hw₁₂
    refine ⟨fs₁ ∩ fs₂, by grind, w₁, ?_, ?_⟩
    · rw [← hw₁, ← fs₁.sum_inter_add_sum_diff fs₂, eq_comm]
      convert add_zero _
      refine Finset.sum_eq_zero ?_
      intro i hi
      rw [← Set.indicator_of_mem (s := ↑fs₁) (by grind) w₁, ha, Set.indicator_of_notMem (by grind)]
    · rw [affineCombination_indicator_subset w₁ p Finset.inter_subset_left]
      refine affineCombination_congr (k := k) (P := P) _ ?_ (fun _ _ ↦ rfl)
      intro i hi
      rw [coe_inter, ← Set.indicator_indicator, Set.indicator_of_mem (by simpa using hi),
        Set.indicator_apply]
      simp only [mem_coe, left_eq_ite_iff]
      intro hi₂
      rw [← Set.indicator_of_mem (s := ↑fs₁) (by simpa using hi) w₁, ha]
      simp [hi₂]
  · grind

