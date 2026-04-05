import Mathlib

variable {α : Type*} {s t : Set α} {a : α}

theorem star_empty [Star α] : (∅ : Set α)⋆ = ∅ := rfl

