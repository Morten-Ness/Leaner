import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [MulPosReflectLT G₀] {a b c : G₀}

theorem mul_inv_le_of_le_mul₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c * b) : a * b⁻¹ ≤ c := by
  obtain rfl | hb := hb.eq_or_lt
  · simp [hc]
  · rwa [mul_inv_le_iff₀ hb]

