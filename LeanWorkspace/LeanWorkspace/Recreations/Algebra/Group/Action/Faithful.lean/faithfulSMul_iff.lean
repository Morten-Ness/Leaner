import Mathlib

variable {M G α : Type*}

theorem faithfulSMul_iff [Group G] [MulAction G α] :
    FaithfulSMul G α ↔ (∀ g : G, (∀ a : α, g • a = a) → g = 1) := by
  refine ⟨fun h a ha ↦ h.eq_of_smul_eq_smul ?_, fun h ↦ ⟨fun {a₁ a₂} h' ↦ ?_⟩⟩
  · simpa only [one_smul]
  · rw [← inv_inv a₂, eq_inv_of_mul_eq_one_left (h (a₂⁻¹ * a₁) ?_), inv_inv]
    simpa only [mul_smul, inv_smul_eq_iff] using h'

