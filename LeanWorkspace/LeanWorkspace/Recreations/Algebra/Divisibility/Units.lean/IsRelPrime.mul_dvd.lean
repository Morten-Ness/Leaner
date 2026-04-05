import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

variable [DecompositionMonoid α]

theorem IsRelPrime.mul_dvd (H : IsRelPrime x y) (H1 : x ∣ z) (H2 : y ∣ z) : x * y ∣ z := H.mul_dvd_of_left_isPrimal H1 H2 (DecompositionMonoid.primal x)

