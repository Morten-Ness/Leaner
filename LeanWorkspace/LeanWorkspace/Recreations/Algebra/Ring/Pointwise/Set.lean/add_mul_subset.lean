import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [Distrib α] (s t u : Set α)

theorem add_mul_subset : (s + t) * u ⊆ s * u + t * u := image2_distrib_subset_right add_mul

