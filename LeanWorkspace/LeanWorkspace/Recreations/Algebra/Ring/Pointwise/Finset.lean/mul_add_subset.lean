import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [DecidableEq α] [Distrib α] (s t u : Finset α)

theorem mul_add_subset : s * (t + u) ⊆ s * t + s * u := image₂_distrib_subset_left mul_add

