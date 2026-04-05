import Mathlib

theorem num_div_den (q : ℚ≥0) : (q.num : ℚ≥0) / q.den = q := by
  ext1
  rw [coe_div, coe_natCast, coe_natCast, num, ← Int.cast_natCast]
  exact (cast_def _).symm

