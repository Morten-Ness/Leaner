import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem dvd_lcm_left [GCDMonoid α] (a b : α) : a ∣ lcm a b := (lcm_dvd_iff.1 (dvd_refl (lcm a b))).1

