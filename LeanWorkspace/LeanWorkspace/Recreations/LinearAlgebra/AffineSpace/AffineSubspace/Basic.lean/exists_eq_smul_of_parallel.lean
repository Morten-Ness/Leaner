import Mathlib

variable {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

theorem exists_eq_smul_of_parallel {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h₂ : p₂ ∉ line[k, p₁, p₃])
    (h₁₂₄₅ : line[k, p₁, p₂] ∥ line[k, p₄, p₅])
    (h₂₃₅₆ : line[k, p₅, p₆].direction ≤ line[k, p₂, p₃].direction)
    (h₃₁₆₄ : line[k, p₆, p₄].direction ≤ line[k, p₃, p₁].direction) :
    ∃ r : k, r ≠ 0 ∧ p₅ -ᵥ p₄ = r • (p₂ -ᵥ p₁) ∧ p₆ -ᵥ p₅ = r • (p₃ -ᵥ p₂) ∧
      p₄ -ᵥ p₆ = r • (p₁ -ᵥ p₃) := by
  rw [AffineSubspace.affineSpan_pair_parallel_iff_exists_unit_smul'] at h₁₂₄₅
  rw [AffineSubspace.direction_affineSpan_pair_le_iff_exists_smul] at h₂₃₅₆ h₃₁₆₄
  obtain ⟨r₁, hr₁⟩ := h₁₂₄₅
  obtain ⟨r₂, hr₂⟩ := h₂₃₅₆
  obtain ⟨r₃, hr₃⟩ := h₃₁₆₄
  rw [Units.smul_def] at hr₁
  by_cases h : (r₁ : k) = r₂
  · refine ⟨r₁, r₁.ne_zero, hr₁.symm, h ▸ hr₂.symm, ?_⟩
    rw [← neg_inj, neg_vsub_eq_vsub_rev, ← smul_neg, neg_vsub_eq_vsub_rev,
      ← vsub_add_vsub_cancel p₆ p₅ p₄, ← vsub_add_vsub_cancel p₃ p₂ p₁, smul_add, hr₁, h, hr₂]
  · exfalso
    have h₁₂ : (r₁ : k) • (p₂ -ᵥ p₁) + r₂ • (p₃ -ᵥ p₂) ∈ vectorSpan k {p₁, p₃} := by
      rw [hr₁, hr₂, add_comm, vsub_add_vsub_cancel, ← neg_vsub_eq_vsub_rev, neg_mem_iff, ← hr₃]
      exact smul_vsub_mem_vectorSpan_pair _ _ _
    have h₁₁ : (r₁ : k) • (p₂ -ᵥ p₁) + (r₁ : k) • (p₃ -ᵥ p₂) ∈ vectorSpan k {p₁, p₃} := by
      rw [add_comm, ← smul_add, vsub_add_vsub_cancel]
      exact smul_vsub_rev_mem_vectorSpan_pair _ _ _
    have h₂₁ : (r₂ - r₁) • (p₃ -ᵥ p₂) ∈ vectorSpan k {p₁, p₃} := by
      simpa [sub_smul] using sub_mem h₁₂ h₁₁
    rw [Submodule.smul_mem_iff _ (by rwa [sub_ne_zero, ne_comm]), ← direction_affineSpan,
      AffineSubspace.vsub_left_mem_direction_iff_mem (right_mem_affineSpan_pair _ _ _)] at h₂₁
    exact h₂ h₂₁

