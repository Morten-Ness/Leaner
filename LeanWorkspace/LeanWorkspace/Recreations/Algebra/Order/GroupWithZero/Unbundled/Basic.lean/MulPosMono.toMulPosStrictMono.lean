import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [MonoidWithZero α]

variable [PartialOrder α]

theorem MulPosMono.toMulPosStrictMono [IsRightCancelMulZero α] [MulPosMono α] :
    MulPosStrictMono α where
  mul_lt_mul_of_pos_right _a ha _b _c hbc := (mul_le_mul_of_nonneg_right hbc.le ha.le).lt_of_ne (hbc.ne ∘ mul_right_cancel₀ ha.ne')

