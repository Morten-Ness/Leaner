import Mathlib

variable {F α β γ : Type*}

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

theorem subset_pow (hs : 1 ∈ s) (hn : n ≠ 0) : s ⊆ s ^ n := by
  simpa using Set.pow_subset_pow_right hs <| Nat.one_le_iff_ne_zero.2 hn

