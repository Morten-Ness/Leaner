import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [MonoidWithZero α]

variable [PartialOrder α]

theorem PosMulMono.toPosMulStrictMono [IsLeftCancelMulZero α] [PosMulMono α] :
    PosMulStrictMono α where
  mul_lt_mul_of_pos_left _a ha _b _c hbc := (mul_le_mul_of_nonneg_left hbc.le ha.le).lt_of_ne (hbc.ne ∘ mul_left_cancel₀ ha.ne')

