import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_one_right' [GCDMonoid α] (a : α) : Associated (gcd a 1) 1 := by simp

