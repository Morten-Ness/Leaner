import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem lcm_eq_of_associated_left [NormalizedGCDMonoid α] {m n : α} (h : Associated m n) (k : α) :
    lcm m k = lcm n k := dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _) (lcm_dvd_lcm h.dvd dvd_rfl)
    (lcm_dvd_lcm h.symm.dvd dvd_rfl)

