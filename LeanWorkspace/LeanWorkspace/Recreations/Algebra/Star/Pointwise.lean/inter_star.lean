import Mathlib

variable {α : Type*} {s t : Set α} {a : α}

theorem inter_star [Star α] : (s ∩ t)⋆ = s⋆ ∩ t⋆ := preimage_inter

