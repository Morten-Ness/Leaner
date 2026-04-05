import Mathlib

variable {α : Type*} {s t : Set α} {a : α}

theorem star_subset_star [InvolutiveStar α] {s t : Set α} : s⋆ ⊆ t⋆ ↔ s ⊆ t := Equiv.star.surjective.preimage_subset_preimage_iff

