import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

theorem IsRelPrime.dvd_of_dvd_mul_left_of_isPrimal (H1 : IsRelPrime x y) (H2 : x ∣ y * z)
    (h : IsPrimal x) : x ∣ z := H1.dvd_of_dvd_mul_right_of_isPrimal (mul_comm y z ▸ H2) h

