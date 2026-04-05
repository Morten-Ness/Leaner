import Mathlib

variable {α : Type*} {s t : Set α} {a : α}

theorem union_star [Star α] : (s ∪ t)⋆ = s⋆ ∪ t⋆ := preimage_union

