import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_comm [NormalizedGCDMonoid α] (a b : α) : gcd a b = gcd b a := dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
    (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))
    (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))

