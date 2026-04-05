import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

variable (hu : IsUnit x)

theorem isRelPrime_mul_unit_left_right : IsRelPrime y (x * z) ↔ IsRelPrime y z := by
  rw [isRelPrime_comm, isRelPrime_mul_unit_left_left hu, isRelPrime_comm]

