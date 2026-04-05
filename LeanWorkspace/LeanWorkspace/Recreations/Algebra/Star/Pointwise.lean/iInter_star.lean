import Mathlib

variable {α : Type*} {s t : Set α} {a : α}

theorem iInter_star {ι : Sort*} [Star α] (s : ι → Set α) : (⋂ i, s i)⋆ = ⋂ i, (s i)⋆ := preimage_iInter

