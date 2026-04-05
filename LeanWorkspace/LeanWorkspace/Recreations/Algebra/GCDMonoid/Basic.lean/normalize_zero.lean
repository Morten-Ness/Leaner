import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [NormalizationMonoid α]

theorem normalize_zero : normalize (0 : α) = 0 := normalize.map_zero

