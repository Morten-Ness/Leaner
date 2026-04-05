import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [NormalizationMonoid α]

theorem normalize_apply (x : α) : normalize x = x * normUnit x := rfl

