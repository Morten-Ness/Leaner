import Mathlib

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem inv_mul_eq_inv_mul_iff_mul_eq_mul : b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b := by
  rw [← div_eq_inv_mul, ← div_eq_inv_mul, div_eq_div_iff_mul_eq_mul]

