import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem inter_pow_subset : (s ∩ t) ^ n ⊆ s ^ n ∩ t ^ n := by apply subset_inter <;> gcongr <;> simp

