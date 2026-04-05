import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [CommSemigroup α] {s t : Finset α}

theorem inter_mul_union_subset : s ∩ t * (s ∪ t) ⊆ s * t := image₂_inter_union_subset mul_comm

