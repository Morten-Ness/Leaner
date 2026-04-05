import Mathlib

variable {F α β γ : Type*}

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

theorem pow_subset_pow_left (hst : s ⊆ t) : s ^ n ⊆ t ^ n := pow_left_mono _ hst

