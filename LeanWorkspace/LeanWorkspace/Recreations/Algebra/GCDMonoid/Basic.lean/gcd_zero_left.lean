import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_zero_left [NormalizedGCDMonoid α] (a : α) : gcd 0 a = normalize a := gcd_eq_normalize (gcd_dvd_right 0 a) (dvd_gcd (dvd_zero _) (dvd_refl a))

