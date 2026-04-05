import Mathlib

theorem eq_of_associated_of_nonneg {a b : ℤ} (h : Associated a b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a = b := dvd_antisymm_of_normalize_eq (Int.normalize_of_nonneg ha) (Int.normalize_of_nonneg hb) h.dvd h.symm.dvd

