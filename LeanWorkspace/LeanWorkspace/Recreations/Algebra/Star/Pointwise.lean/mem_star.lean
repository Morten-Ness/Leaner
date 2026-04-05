import Mathlib

variable {α : Type*} {s t : Set α} {a : α}

theorem mem_star [Star α] : a ∈ s⋆ ↔ a⋆ ∈ s := Iff.rfl

