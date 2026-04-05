import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem Irreducible.gcd_eq_one_iff [NormalizedGCDMonoid α] {x y : α} (hx : Irreducible x) :
    gcd x y = 1 ↔ ¬(x ∣ y) := by
  rw [← hx.isUnit_gcd_iff, ← normalize_eq_one, NormalizedGCDMonoid.normalize_gcd]

