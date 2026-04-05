import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [MulPosReflectLT G₀] {a b c : G₀}

theorem mul_le_of_le_mul_inv₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b * c⁻¹) : a * c ≤ b := by
  obtain rfl | hc := hc.eq_or_lt
  · simpa using hb
  · rwa [le_mul_inv_iff₀ hc] at h

