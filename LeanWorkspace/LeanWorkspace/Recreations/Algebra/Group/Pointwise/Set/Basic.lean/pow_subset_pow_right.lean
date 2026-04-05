import Mathlib

variable {F α β γ : Type*}

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

theorem pow_subset_pow_right (hs : 1 ∈ s) (hmn : m ≤ n) : s ^ m ⊆ s ^ n := Set.pow_right_monotone hs hmn

