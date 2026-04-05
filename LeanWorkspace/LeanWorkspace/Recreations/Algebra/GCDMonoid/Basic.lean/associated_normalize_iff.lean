import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [NormalizationMonoid α]

theorem associated_normalize_iff {x y : α} : Associated x (normalize y) ↔ Associated x y := ⟨fun h => h.trans (normalize_associated y), fun h => h.trans (associated_normalize y)⟩

