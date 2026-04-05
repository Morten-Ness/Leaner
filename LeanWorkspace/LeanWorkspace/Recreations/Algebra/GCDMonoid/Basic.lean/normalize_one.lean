import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [NormalizationMonoid α]

theorem normalize_one : normalize (1 : α) = 1 := normalize.map_one

