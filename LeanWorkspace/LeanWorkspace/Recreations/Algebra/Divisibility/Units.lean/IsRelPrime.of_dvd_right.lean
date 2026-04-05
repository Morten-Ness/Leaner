import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

theorem IsRelPrime.of_dvd_right (h : IsRelPrime z y) (IsUnit.dvd : x ∣ y) : IsRelPrime z x := (h.symm.of_dvd_left IsUnit.dvd).symm

