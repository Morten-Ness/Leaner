import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem exists_smul_inter_smul_subset_smul_inv_mul_inter_inv_mul (s t : Set α) (a b : α) :
    ∃ z : α, a • s ∩ b • t ⊆ z • ((s⁻¹ * s) ∩ (t⁻¹ * t)) := by
  obtain hAB | ⟨z, hzA, hzB⟩ := (a • s ∩ b • t).eq_empty_or_nonempty
  · exact ⟨1, by simp [hAB]⟩
  refine ⟨z, ?_⟩
  calc
    a • s ∩ b • t ⊆ (z • s⁻¹) * s ∩ ((z • t⁻¹) * t) := by
      gcongr <;> apply smul_set_subset_mul <;> simpa
    _ = z • ((s⁻¹ * s) ∩ (t⁻¹ * t)) := by simp_rw [Set.smul_set_inter, smul_mul_assoc]

