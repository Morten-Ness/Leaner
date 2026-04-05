import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [NormalizationMonoid α]

theorem Associated.eq_of_normalized [IsCancelMulZero α]
    {a b : α} (h : Associated a b) (ha : normalize a = a) (hb : normalize b = b) :
    a = b := dvd_antisymm_of_normalize_eq ha hb h.dvd h.dvd'

