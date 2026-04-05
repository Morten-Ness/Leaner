import Mathlib

variable {α : Type*} {s t : Set α} {a : α}

theorem compl_star [Star α] : sᶜ⋆ = s⋆ᶜ := preimage_compl

