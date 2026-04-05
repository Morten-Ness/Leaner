import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [Distrib α] (s t u : Set α)

theorem mul_add_subset : s * (t + u) ⊆ s * t + s * u := image2_distrib_subset_left mul_add

