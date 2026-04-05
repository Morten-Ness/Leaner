import Mathlib

variable {α : Type*}

variable [Mul α] [PartialOrder α] [MulLeftStrictMono α] [MulRightStrictMono α]

theorem Ico_mul_Icc_subset' (a b c d : α) : Ico a b * Icc c d ⊆ Ico (a * c) (b * d) := by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_le_mul' hya hzc, mul_lt_mul_of_lt_of_le hyb hzd⟩

