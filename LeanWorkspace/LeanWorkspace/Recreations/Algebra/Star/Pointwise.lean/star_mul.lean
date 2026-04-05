import Mathlib

variable {α : Type*} {s t : Set α} {a : α}

theorem star_mul [Mul α] [StarMul α] (s t : Set α) : (s * t)⋆ = t⋆ * s⋆ := by
  simp_rw [← Set.image_star, ← image2_mul, image_image2, image2_image_left, image2_image_right,
    star_mul, image2_swap _ s t]

