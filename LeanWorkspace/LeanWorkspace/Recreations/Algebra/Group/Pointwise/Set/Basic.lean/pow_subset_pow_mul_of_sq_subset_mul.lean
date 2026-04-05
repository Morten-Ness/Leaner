import Mathlib

variable {F α β γ : Type*}

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

theorem pow_subset_pow_mul_of_sq_subset_mul (hst : s ^ 2 ⊆ t * s) (hn : n ≠ 0) :
    s ^ n ⊆ t ^ (n - 1) * s := pow_le_pow_mul_of_sq_le_mul hst hn

