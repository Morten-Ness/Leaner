import Mathlib

variable {α : Type*}

variable [Mul α] [PartialOrder α] [MulLeftStrictMono α] [MulRightStrictMono α]

theorem Iic_mul_Iio_subset' (a b : α) : Iic a * Iio b ⊆ Iio (a * b) := by
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_lt_mul_of_le_of_lt hya hzb

