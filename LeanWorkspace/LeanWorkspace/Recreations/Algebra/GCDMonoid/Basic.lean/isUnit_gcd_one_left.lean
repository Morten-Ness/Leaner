import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem isUnit_gcd_one_left [GCDMonoid α] (a : α) : IsUnit (gcd 1 a) := isUnit_of_dvd_one (gcd_dvd_left _ _)

