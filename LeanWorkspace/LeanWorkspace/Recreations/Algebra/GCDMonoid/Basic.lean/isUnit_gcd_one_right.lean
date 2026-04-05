import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem isUnit_gcd_one_right [GCDMonoid α] (a : α) : IsUnit (gcd a 1) := isUnit_of_dvd_one (gcd_dvd_right _ _)

