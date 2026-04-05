import Mathlib

variable {α : Type*}

variable [Mul α] [Preorder α] [MulLeftMono α] [MulRightMono α]

theorem Iic_mul_Iic_subset' (a b : α) : Iic a * Iic b ⊆ Iic (a * b) := by
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_le_mul' hya hzb

