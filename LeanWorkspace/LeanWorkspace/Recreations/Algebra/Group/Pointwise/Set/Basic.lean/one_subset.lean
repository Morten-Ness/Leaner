import Mathlib

variable {F α β γ : Type*}

variable [One α] {s : Set α} {a : α}

theorem one_subset : 1 ⊆ s ↔ (1 : α) ∈ s := singleton_subset_iff

