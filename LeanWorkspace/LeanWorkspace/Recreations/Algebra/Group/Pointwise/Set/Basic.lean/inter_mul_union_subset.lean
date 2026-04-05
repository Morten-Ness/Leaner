import Mathlib

variable {F α β γ : Type*}

variable [CommSemigroup α] {s t : Set α}

theorem inter_mul_union_subset : s ∩ t * (s ∪ t) ⊆ s * t := image2_inter_union_subset mul_comm

