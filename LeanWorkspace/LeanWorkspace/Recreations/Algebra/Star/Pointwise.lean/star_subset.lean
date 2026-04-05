import Mathlib

variable {α : Type*} {s t : Set α} {a : α}

theorem star_subset [InvolutiveStar α] {s t : Set α} : s⋆ ⊆ t ↔ s ⊆ t⋆ := by
  rw [← Set.star_subset_star, star_star]

