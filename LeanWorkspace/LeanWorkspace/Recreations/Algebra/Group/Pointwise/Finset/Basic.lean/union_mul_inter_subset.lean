import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [CommSemigroup α] {s t : Finset α}

theorem union_mul_inter_subset : (s ∪ t) * (s ∩ t) ⊆ s * t := image₂_union_inter_subset mul_comm

