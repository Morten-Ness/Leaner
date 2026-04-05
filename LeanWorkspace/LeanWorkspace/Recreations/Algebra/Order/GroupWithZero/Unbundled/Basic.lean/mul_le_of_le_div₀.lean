import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [MulPosReflectLT G₀] {a b c : G₀}

theorem mul_le_of_le_div₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b / c) : a * c ≤ b := mul_le_of_le_mul_inv₀ hb hc (div_eq_mul_inv b _ ▸ h)

