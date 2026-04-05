import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [NormalizationMonoid α]

theorem normalize_associated_iff {x y : α} : Associated (normalize x) y ↔ Associated x y := ⟨fun h => (associated_normalize _).trans h, fun h => (normalize_associated _).trans h⟩

