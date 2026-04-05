import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_ne_zero_of_right [GCDMonoid α] {a b : α} (hb : b ≠ 0) : gcd a b ≠ 0 := by
  simp_all

