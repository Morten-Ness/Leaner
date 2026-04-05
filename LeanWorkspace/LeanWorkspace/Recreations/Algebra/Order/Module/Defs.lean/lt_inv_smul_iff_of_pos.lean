import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [GroupWithZero α] [Preorder α] [Preorder β] [MulAction α β]

theorem lt_inv_smul_iff_of_pos [PosSMulStrictMono α β] [PosSMulReflectLT α β] (ha : 0 < a) :
    b₁ < a⁻¹ • b₂ ↔ a • b₁ < b₂ := by rw [← smul_lt_smul_iff_of_pos_left ha, smul_inv_smul₀ ha.ne']

