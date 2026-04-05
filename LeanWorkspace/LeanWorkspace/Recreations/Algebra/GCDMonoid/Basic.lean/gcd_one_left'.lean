import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_one_left' [GCDMonoid α] (a : α) : Associated (gcd 1 a) 1 := by simp

