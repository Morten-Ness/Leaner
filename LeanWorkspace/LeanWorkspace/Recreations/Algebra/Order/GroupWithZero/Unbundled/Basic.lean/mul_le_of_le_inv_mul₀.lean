import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] {a b c : G₀}

theorem mul_le_of_le_inv_mul₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c⁻¹ * b) : c * a ≤ b := by
  obtain rfl | hc := hc.eq_or_lt
  · simpa using hb
  · rwa [le_inv_mul_iff₀ hc] at h

