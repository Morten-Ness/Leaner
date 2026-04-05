import Mathlib

variable {α : Type*} {s t : Set α} {a : α}

theorem star_inv' [GroupWithZero α] [StarMul α] (s : Set α) : s⁻¹⋆ = s⋆⁻¹ := by
  ext
  simp only [Set.mem_star, mem_inv, star_inv₀]

