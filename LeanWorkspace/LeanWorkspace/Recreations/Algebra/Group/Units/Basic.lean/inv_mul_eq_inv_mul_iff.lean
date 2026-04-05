import Mathlib

variable {α : Type u}

variable [CommMonoid α] (a c : α) (b d : αˣ)

theorem inv_mul_eq_inv_mul_iff : b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b := by
  rw [mul_comm, mul_comm _ c, Units.mul_inv_eq_mul_inv_iff]

