import Mathlib

theorem inv_def (q : ℚ≥0) : q⁻¹ = divNat q.den q.num := by ext; simp [Rat.inv_def, num_coe, den_coe]

