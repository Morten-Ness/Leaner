import Mathlib

variable {α : Type u}

variable [CommMonoid α]

theorem divp_mul_divp (x y : α) (ux uy : αˣ) : x /ₚ ux * (y /ₚ uy) = x * y /ₚ (ux * uy) := by
  rw [divp_mul_eq_mul_divp, ← divp_assoc, divp_divp_eq_divp_mul]

