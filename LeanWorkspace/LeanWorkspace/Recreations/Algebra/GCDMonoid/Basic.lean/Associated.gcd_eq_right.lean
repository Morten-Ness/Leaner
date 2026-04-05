import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem Associated.gcd_eq_right [NormalizedGCDMonoid α] {m n : α} (h : Associated m n) (k : α) :
    gcd k m = gcd k n := dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) (gcd_dvd_gcd dvd_rfl h.dvd)
    (gcd_dvd_gcd dvd_rfl h.symm.dvd)

