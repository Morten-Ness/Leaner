import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

variable (hu : IsUnit x)

theorem isRelPrime_mul_unit_right_right : IsRelPrime y (z * x) ↔ IsRelPrime y z := by
  rw [mul_comm, isRelPrime_mul_unit_left_right hu]

