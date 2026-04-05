import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [DecidableEq α] [Distrib α] (s t u : Finset α)

theorem add_mul_subset : (s + t) * u ⊆ s * u + t * u := image₂_distrib_subset_right add_mul

