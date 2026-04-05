import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [NormalizationMonoid α]

theorem normalize_associated (x : α) : Associated (normalize x) x := (associated_normalize _).symm

