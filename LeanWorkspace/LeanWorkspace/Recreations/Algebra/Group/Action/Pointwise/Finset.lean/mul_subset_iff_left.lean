import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Mul α] [DecidableEq α] {s t u : Finset α} {a : α}

theorem mul_subset_iff_left : s * t ⊆ u ↔ ∀ a ∈ s, a • t ⊆ u := image₂_subset_iff_left

