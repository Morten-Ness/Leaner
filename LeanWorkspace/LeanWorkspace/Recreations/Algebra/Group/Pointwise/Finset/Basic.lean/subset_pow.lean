import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem subset_pow (hs : 1 ∈ s) (hn : n ≠ 0) : s ⊆ s ^ n := by
  simpa using Finset.pow_subset_pow_right hs <| Nat.one_le_iff_ne_zero.2 hn

