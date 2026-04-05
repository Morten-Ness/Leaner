import Mathlib

theorem natCast_eq_divInt (n : ℕ) : ↑n = n /. 1 := by rw [← Int.cast_natCast, intCast_eq_divInt]

