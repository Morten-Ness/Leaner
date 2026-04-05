import Mathlib

variable {F α β : Type*}

variable [MulOneClass α] [MulOneClass β] [FunLike F α β] [MonoidHomClass F α β]

theorem IsSquare.map {a : α} (f : F) : IsSquare a → IsSquare (f a) := fun ⟨r, _⟩ => ⟨f r, by simp [*]⟩

