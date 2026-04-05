import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] {a b c : G₀}

theorem inv_mul_le_of_le_mul₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b * c) : b⁻¹ * a ≤ c := by
  obtain rfl | hb := hb.eq_or_lt
  · simp [hc]
  · rwa [inv_mul_le_iff₀ hb]

