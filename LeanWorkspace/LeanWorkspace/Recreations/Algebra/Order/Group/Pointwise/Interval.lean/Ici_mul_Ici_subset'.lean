import Mathlib

variable {α : Type*}

variable [Mul α] [Preorder α] [MulLeftMono α] [MulRightMono α]

theorem Ici_mul_Ici_subset' (a b : α) : Ici a * Ici b ⊆ Ici (a * b) := by
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_le_mul' hya hzb

