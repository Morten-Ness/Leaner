import Mathlib

variable {α : Type*}

variable [Mul α] [PartialOrder α] [MulLeftStrictMono α] [MulRightStrictMono α]

theorem Ico_mul_Ioc_subset' (a b c d : α) : Ico a b * Ioc c d ⊆ Ioo (a * c) (b * d) := by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_lt_mul_of_le_of_lt hya hzc, mul_lt_mul_of_lt_of_le hyb hzd⟩

