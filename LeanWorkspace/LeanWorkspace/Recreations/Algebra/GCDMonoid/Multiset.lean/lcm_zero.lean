import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem lcm_zero : (0 : Multiset α).lcm = 1 := fold_zero _ _

