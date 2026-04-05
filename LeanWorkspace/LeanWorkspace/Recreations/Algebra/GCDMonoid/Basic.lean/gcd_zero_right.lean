import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_zero_right [NormalizedGCDMonoid α] (a : α) : gcd a 0 = normalize a := gcd_eq_normalize (gcd_dvd_left a 0) (dvd_gcd (dvd_refl a) (dvd_zero _))

