import Mathlib

variable {G M A B α β : Type*}

variable [Group α] [MulAction α β]

theorem isCancelSMul_iff_eq_one_of_smul_eq :
    IsCancelSMul α β ↔ (∀ (g : α) (x : β), g • x = x → g = 1) := by
  refine ⟨fun H _ _ ↦ IsCancelSMul.eq_one_of_smul, fun H ↦ ⟨fun g h x ↦ ?_⟩⟩
  rw [smul_eq_iff_eq_inv_smul, eq_comm, ← mul_smul, ← inv_mul_eq_one (G := α)]
  exact H (g⁻¹ * h) x

