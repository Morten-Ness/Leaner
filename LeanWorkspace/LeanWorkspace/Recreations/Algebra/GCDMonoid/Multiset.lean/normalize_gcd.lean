import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem normalize_gcd (s : Multiset α) : normalize s.gcd = s.gcd := Multiset.induction_on s (by simp) fun a s _ ↦ by simp

