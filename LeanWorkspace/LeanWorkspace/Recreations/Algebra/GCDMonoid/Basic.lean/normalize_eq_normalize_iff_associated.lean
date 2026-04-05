import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [NormalizationMonoid α]

theorem normalize_eq_normalize_iff_associated [IsCancelMulZero α] {x y : α} :
    normalize x = normalize y ↔ Associated x y := by
  rw [normalize_eq_normalize_iff, dvd_dvd_iff_associated]

