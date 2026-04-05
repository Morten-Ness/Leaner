import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem pow_subset_pow_right (hs : 1 ∈ s) (hmn : m ≤ n) : s ^ m ⊆ s ^ n := Finset.pow_right_monotone hs hmn

