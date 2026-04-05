import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [MulPosReflectLT G₀] {a b c : G₀}

theorem div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a ≤ b) (hb : 0 ≤ b) : a / b ≤ 1 := div_le_of_le_mul₀ hb zero_le_one <| by rwa [one_mul]

