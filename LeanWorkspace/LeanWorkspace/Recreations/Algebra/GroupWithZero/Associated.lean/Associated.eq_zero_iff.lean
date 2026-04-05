import Mathlib

variable {M : Type*}

theorem Associated.eq_zero_iff [MonoidWithZero M] {a b : M} (h : a ~ᵤ b) : a = 0 ↔ b = 0 := by
  obtain ⟨u, Associated.rfl⟩ := h
  rw [← Units.eq_mul_inv_iff_mul_eq, zero_mul]

