import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem lcm_singleton {a : α} : ({a} : Multiset α).lcm = normalize a := (fold_singleton _ _ _).trans <| lcm_one_right _

