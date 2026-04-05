import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

variable [DecompositionMonoid α]

theorem IsRelPrime.dvd_of_dvd_mul_right (H1 : IsRelPrime x z) (H2 : x ∣ y * z) : x ∣ y := H1.dvd_of_dvd_mul_right_of_isPrimal H2 (DecompositionMonoid.primal x)

