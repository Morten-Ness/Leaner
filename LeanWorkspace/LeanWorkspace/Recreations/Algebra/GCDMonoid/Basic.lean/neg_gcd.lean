import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

variable [HasDistribNeg α]

theorem neg_gcd [NormalizedGCDMonoid α] {a b : α} : gcd (-a) b = gcd a b := neg_gcd'.eq_of_normalized (normalize_gcd _ _) (normalize_gcd _ _)

