import Mathlib

variable {α : Type*} {s t : Set α} {a : α}

theorem star_singleton {β : Type*} [InvolutiveStar β] (x : β) : ({x} : Set β)⋆ = {x⋆} := by
  ext1 y
  rw [Set.mem_star, mem_singleton_iff, mem_singleton_iff, star_eq_iff_star_eq, eq_comm]

