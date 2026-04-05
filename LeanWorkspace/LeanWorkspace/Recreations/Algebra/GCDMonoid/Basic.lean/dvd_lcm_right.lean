import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem dvd_lcm_right [GCDMonoid α] (a b : α) : b ∣ lcm a b := (lcm_dvd_iff.1 (dvd_refl (lcm a b))).2

