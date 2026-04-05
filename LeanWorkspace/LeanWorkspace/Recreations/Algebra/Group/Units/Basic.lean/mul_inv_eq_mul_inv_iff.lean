import Mathlib

variable {α : Type u}

variable [CommMonoid α] (a c : α) (b d : αˣ)

theorem mul_inv_eq_mul_inv_iff : a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b := by
  rw [mul_comm c, Units.mul_inv_eq_iff_eq_mul, mul_assoc, Units.eq_inv_mul_iff_mul_eq, mul_comm]

