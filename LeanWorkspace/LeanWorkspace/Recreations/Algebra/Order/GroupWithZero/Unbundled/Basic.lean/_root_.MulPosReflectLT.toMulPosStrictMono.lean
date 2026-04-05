import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [MulPosReflectLT G₀] {a b c : G₀}

theorem _root_.MulPosReflectLT.toMulPosStrictMono : MulPosStrictMono G₀ where
  mul_lt_mul_of_pos_right a ha b c hbc := lt_of_mul_lt_mul_right (by simpa [ha.ne']) (Right.inv_pos.2 ha).le

