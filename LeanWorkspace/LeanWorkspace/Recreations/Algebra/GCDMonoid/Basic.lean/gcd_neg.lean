import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

variable [HasDistribNeg α]

theorem gcd_neg [NormalizedGCDMonoid α] {a b : α} : gcd a (-b) = gcd a b := gcd_neg'.eq_of_normalized (normalize_gcd _ _) (normalize_gcd _ _)

