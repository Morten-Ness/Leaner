import Mathlib

variable {F α β γ : Type*}

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

theorem pow_subset_pow (hst : s ⊆ t) (ht : 1 ∈ t) (hmn : m ≤ n) : s ^ m ⊆ t ^ n := (Set.pow_subset_pow_left hst).trans (Set.pow_subset_pow_right ht hmn)

