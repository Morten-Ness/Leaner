import Mathlib

variable {α : Type*} {s t : Set α} {a : α}

theorem image_star [InvolutiveStar α] : Star.star '' s = s⋆ := by
  simp only [← Set.star_preimage]
  rw [image_eq_preimage_of_inverse] <;> intro <;> simp only [star_star]

