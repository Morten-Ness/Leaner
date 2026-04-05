import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem Associated.gcd_eq_left [NormalizedGCDMonoid α] {m n : α} (h : Associated m n) (k : α) :
    gcd m k = gcd n k := dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) (gcd_dvd_gcd h.dvd dvd_rfl)
    (gcd_dvd_gcd h.symm.dvd dvd_rfl)

