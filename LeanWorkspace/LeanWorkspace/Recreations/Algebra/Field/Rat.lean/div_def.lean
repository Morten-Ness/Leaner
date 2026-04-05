import Mathlib

theorem div_def (p q : ℚ≥0) : p / q = divNat (p.num * q.den) (p.den * q.num) := by
  ext; simp [Rat.div_def', num_coe, den_coe]

