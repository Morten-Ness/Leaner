import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_zero_right' [GCDMonoid α] (a : α) : Associated (gcd a 0) a := associated_of_dvd_dvd (gcd_dvd_left a 0) (dvd_gcd (dvd_refl a) (dvd_zero _))

