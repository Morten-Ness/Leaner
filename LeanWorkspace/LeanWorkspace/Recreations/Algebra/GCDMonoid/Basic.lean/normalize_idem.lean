import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [NormalizationMonoid α]

theorem normalize_idem (x : α) : normalize (normalize x) = normalize x := by simp [normalize_apply]

