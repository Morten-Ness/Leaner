import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_zero_left' [GCDMonoid α] (a : α) : Associated (gcd 0 a) a := associated_of_dvd_dvd (gcd_dvd_right 0 a) (dvd_gcd (dvd_zero _) (dvd_refl a))

