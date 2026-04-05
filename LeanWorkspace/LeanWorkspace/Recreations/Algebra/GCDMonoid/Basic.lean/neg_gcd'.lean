import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

variable [HasDistribNeg α]

theorem neg_gcd' [GCDMonoid α] {a b : α} : Associated (gcd (-a) b) (gcd a b) := Associated.gcd (.neg_left .rfl) .rfl

