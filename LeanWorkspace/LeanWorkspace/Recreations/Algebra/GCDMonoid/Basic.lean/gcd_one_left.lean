import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_one_left [NormalizedGCDMonoid α] (a : α) : gcd 1 a = 1 := dvd_antisymm_of_normalize_eq (normalize_gcd _ _) normalize_one (gcd_dvd_left _ _) (one_dvd _)

