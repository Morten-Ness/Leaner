import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem lcm_same [NormalizedGCDMonoid α] (a : α) : lcm a a = normalize a := lcm_eq_normalize (lcm_dvd dvd_rfl dvd_rfl) (dvd_lcm_left _ _)

