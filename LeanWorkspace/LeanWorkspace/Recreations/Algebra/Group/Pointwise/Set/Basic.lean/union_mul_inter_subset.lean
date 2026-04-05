import Mathlib

variable {F α β γ : Type*}

variable [CommSemigroup α] {s t : Set α}

theorem union_mul_inter_subset : (s ∪ t) * (s ∩ t) ⊆ s * t := image2_union_inter_subset mul_comm

