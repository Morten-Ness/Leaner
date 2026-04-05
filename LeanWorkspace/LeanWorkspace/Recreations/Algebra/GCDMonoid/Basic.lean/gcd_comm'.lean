import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_comm' [GCDMonoid α] (a b : α) : Associated (gcd a b) (gcd b a) := associated_of_dvd_dvd (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))
    (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))

