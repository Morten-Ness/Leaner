import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem pow_subset_pow_left (hst : s ⊆ t) : s ^ n ⊆ t ^ n := subset_of_le (pow_left_mono n hst)

