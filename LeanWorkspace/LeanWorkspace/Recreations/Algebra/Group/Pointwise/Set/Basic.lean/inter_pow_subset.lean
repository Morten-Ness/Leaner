import Mathlib

variable {F α β γ : Type*}

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

theorem inter_pow_subset : (s ∩ t) ^ n ⊆ s ^ n ∩ t ^ n := by apply subset_inter <;> gcongr <;> simp

