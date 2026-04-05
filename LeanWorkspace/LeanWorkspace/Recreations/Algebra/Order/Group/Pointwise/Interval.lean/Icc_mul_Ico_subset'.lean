import Mathlib

variable {α : Type*}

variable [Mul α] [PartialOrder α] [MulLeftStrictMono α] [MulRightStrictMono α]

theorem Icc_mul_Ico_subset' (a b c d : α) : Icc a b * Ico c d ⊆ Ico (a * c) (b * d) := by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_le_mul' hya hzc, mul_lt_mul_of_le_of_lt hyb hzd⟩

