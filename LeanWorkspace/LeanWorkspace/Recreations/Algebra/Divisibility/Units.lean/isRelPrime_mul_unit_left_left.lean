import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

variable (hu : IsUnit x)

theorem isRelPrime_mul_unit_left_left : IsRelPrime (x * y) z ↔ IsRelPrime y z := ⟨IsRelPrime.of_mul_left_right, fun H _ h ↦ H (Units.dvd_mul_left hu.mp h)⟩

