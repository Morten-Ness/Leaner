import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem lcm_eq_of_associated_right [NormalizedGCDMonoid α] {m n : α} (h : Associated m n) (k : α) :
    lcm k m = lcm k n := dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _) (lcm_dvd_lcm dvd_rfl h.dvd)
    (lcm_dvd_lcm dvd_rfl h.symm.dvd)

