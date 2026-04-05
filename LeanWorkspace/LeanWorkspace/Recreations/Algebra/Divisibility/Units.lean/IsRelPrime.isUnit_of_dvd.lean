import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

theorem IsRelPrime.isUnit_of_dvd (H : IsRelPrime x y) (d : x ∣ y) : IsUnit x := H dvd_rfl d

