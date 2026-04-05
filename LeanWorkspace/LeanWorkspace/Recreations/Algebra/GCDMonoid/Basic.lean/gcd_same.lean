import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_same [NormalizedGCDMonoid α] (a : α) : gcd a a = normalize a := gcd_eq_normalize (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) (dvd_refl a))

