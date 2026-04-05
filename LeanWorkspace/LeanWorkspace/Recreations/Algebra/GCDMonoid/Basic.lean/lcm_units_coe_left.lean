import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem lcm_units_coe_left [NormalizedGCDMonoid α] (u : αˣ) (a : α) : lcm (↑u) a = normalize a := lcm_eq_normalize (lcm_dvd Units.coe_dvd dvd_rfl) (dvd_lcm_right _ _)

