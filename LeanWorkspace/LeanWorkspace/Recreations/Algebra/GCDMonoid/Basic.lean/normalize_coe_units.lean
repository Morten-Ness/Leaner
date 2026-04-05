import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [NormalizationMonoid α]

theorem normalize_coe_units (u : αˣ) : normalize (u : α) = 1 := by simp [normalize_apply]

