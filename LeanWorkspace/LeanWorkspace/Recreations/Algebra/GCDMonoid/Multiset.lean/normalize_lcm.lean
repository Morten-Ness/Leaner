import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem normalize_lcm (s : Multiset α) : normalize s.lcm = s.lcm := Multiset.induction_on s (by simp) fun a s _ ↦ by simp

