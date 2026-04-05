import Mathlib

variable {M : Type*}

theorem Associated.ne_zero_iff [MonoidWithZero M] {a b : M} (h : a ~ᵤ b) : a ≠ 0 ↔ b ≠ 0 := not_congr h.eq_zero_iff

