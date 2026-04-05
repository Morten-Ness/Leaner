import Mathlib

variable {α : Type*}

variable [Mul α] [PartialOrder α] [MulLeftStrictMono α] [MulRightStrictMono α]

theorem Ioi_mul_Ici_subset' (a b : α) : Ioi a * Ici b ⊆ Ioi (a * b) := by
  have := mulLeftMono_of_mulLeftStrictMono α
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_lt_mul_of_lt_of_le hya hzb

