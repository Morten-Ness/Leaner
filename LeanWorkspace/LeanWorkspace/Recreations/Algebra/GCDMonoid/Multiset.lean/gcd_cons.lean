import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem gcd_cons (a : α) (s : Multiset α) : (a ::ₘ s).gcd = GCDMonoid.gcd a s.gcd := fold_cons_left _ _ _ _

