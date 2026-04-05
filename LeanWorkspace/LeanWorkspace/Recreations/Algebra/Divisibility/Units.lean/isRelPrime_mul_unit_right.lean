import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

variable (hu : IsUnit x)

theorem isRelPrime_mul_unit_right : IsRelPrime (y * x) (z * x) ↔ IsRelPrime y z := by
  rw [isRelPrime_mul_unit_right_left hu, isRelPrime_mul_unit_right_right hu]

