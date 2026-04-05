import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem gcd_singleton {a : α} : ({a} : Multiset α).gcd = normalize a := (fold_singleton _ _ _).trans <| gcd_zero_right _

