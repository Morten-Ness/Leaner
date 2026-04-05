import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem lcm_comm [NormalizedGCDMonoid α] (a b : α) : lcm a b = lcm b a := dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _)
    (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))
    (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))

