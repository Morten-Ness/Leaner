import Mathlib

variable {α : Type*} {s t : Set α} {a : α}

theorem star_add [AddMonoid α] [StarAddMonoid α] (s t : Set α) : (s + t)⋆ = s⋆ + t⋆ := by
  simp_rw [← Set.image_star, ← image2_add, image_image2, image2_image_left, image2_image_right,
    star_add]

