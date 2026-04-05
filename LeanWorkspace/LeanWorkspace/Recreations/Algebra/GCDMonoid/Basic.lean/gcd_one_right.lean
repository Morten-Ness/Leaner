import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_one_right [NormalizedGCDMonoid α] (a : α) : gcd a 1 = 1 := dvd_antisymm_of_normalize_eq (normalize_gcd _ _) normalize_one (gcd_dvd_right _ _) (one_dvd _)

