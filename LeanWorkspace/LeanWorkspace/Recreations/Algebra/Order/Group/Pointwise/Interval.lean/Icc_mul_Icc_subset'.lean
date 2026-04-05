import Mathlib

variable {α : Type*}

variable [Mul α] [Preorder α] [MulLeftMono α] [MulRightMono α]

theorem Icc_mul_Icc_subset' (a b c d : α) : Icc a b * Icc c d ⊆ Icc (a * c) (b * d) := by
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_le_mul' hya hzc, mul_le_mul' hyb hzd⟩

