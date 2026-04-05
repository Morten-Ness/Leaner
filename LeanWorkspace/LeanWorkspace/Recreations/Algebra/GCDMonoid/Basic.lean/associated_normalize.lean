import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [NormalizationMonoid α]

theorem associated_normalize (x : α) : Associated x (normalize x) := ⟨_, rfl⟩

