import Mathlib

theorem one_le_abs {z : ℤ} (h₀ : z ≠ 0) : 1 ≤ |z| := add_one_le_iff.mpr (abs_pos.mpr h₀)

