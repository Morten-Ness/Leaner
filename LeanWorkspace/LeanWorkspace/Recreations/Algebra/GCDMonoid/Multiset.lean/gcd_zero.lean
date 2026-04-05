import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem gcd_zero : (0 : Multiset α).gcd = 0 := fold_zero _ _

