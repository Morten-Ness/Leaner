import Mathlib

variable {α : Type*} {s t : Set α} {a : α}

theorem star_univ [Star α] : (univ : Set α)⋆ = univ := rfl

