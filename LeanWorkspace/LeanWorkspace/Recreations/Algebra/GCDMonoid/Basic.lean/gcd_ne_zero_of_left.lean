import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_ne_zero_of_left [GCDMonoid α] {a b : α} (ha : a ≠ 0) : gcd a b ≠ 0 := by
  simp_all

