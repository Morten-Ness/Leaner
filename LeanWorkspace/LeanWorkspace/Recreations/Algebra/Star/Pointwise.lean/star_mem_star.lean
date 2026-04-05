import Mathlib

variable {α : Type*} {s t : Set α} {a : α}

theorem star_mem_star [InvolutiveStar α] : a⋆ ∈ s⋆ ↔ a ∈ s := by simp only [Set.mem_star, star_star]

