import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem normalize_lcm [NormalizedGCDMonoid α] (a b : α) : normalize (lcm a b) = lcm a b := NormalizedGCDMonoid.normalize_lcm a b

