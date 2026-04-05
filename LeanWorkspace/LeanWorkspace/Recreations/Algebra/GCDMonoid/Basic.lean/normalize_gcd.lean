import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem normalize_gcd [NormalizedGCDMonoid α] : ∀ a b : α, normalize (gcd a b) = gcd a b := NormalizedGCDMonoid.normalize_gcd

