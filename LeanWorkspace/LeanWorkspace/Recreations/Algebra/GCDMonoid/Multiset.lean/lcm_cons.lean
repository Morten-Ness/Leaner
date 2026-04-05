import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem lcm_cons (a : α) (s : Multiset α) : (a ::ₘ s).lcm = GCDMonoid.lcm a s.lcm := fold_cons_left _ _ _ _

