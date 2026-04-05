import Mathlib

theorem abs_negOnePow (n : ℤ) : |(n.negOnePow : ℤ)| = 1 := by
  rw [abs_eq_natAbs, Int.units_natAbs, Nat.cast_one]

