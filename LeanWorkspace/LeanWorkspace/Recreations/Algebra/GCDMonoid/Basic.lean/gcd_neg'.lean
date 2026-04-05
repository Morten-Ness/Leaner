import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

variable [HasDistribNeg α]

theorem gcd_neg' [GCDMonoid α] {a b : α} : Associated (gcd a (-b)) (gcd a b) := Associated.gcd .rfl (.neg_left .rfl)

