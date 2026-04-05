import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

variable [DecompositionMonoid α]

theorem IsRelPrime.dvd_of_dvd_mul_left (H1 : IsRelPrime x y) (H2 : x ∣ y * z) : x ∣ z := H1.dvd_of_dvd_mul_right (mul_comm y z ▸ H2)

