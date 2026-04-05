import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem Irreducible.isUnit_gcd_iff [GCDMonoid α] {x y : α} (hx : Irreducible x) :
    IsUnit (gcd x y) ↔ ¬(x ∣ y) := by
  rw [hx.isUnit_iff_not_associated_of_dvd (gcd_dvd_left x y), not_iff_not, associated_gcd_left_iff]

