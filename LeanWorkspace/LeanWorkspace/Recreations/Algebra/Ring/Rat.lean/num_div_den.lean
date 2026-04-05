import Mathlib

theorem num_div_den (r : ℚ) : (r.num : ℚ) / (r.den : ℚ) = r := by
  rw [← Int.cast_natCast, ← divInt_eq_div, num_divInt_den]

