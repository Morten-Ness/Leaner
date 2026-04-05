import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

theorem IsRelPrime.of_dvd_left (h : IsRelPrime y z) (IsUnit.dvd : x ∣ y) : IsRelPrime x z := by
  obtain ⟨d, rfl⟩ := IsUnit.dvd; exact IsRelPrime.of_mul_left_left h

