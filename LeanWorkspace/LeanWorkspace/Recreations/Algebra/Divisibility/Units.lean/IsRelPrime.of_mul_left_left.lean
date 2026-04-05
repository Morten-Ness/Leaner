import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

theorem IsRelPrime.of_mul_left_left (H : IsRelPrime (x * y) z) : IsRelPrime x z := fun _ hx ↦ H (dvd_mul_of_dvd_left hx _)

