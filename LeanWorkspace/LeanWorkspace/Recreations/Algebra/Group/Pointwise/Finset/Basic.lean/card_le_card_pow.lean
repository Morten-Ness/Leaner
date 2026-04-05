import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [CancelMonoid α] {s : Finset α} {m n : ℕ}

theorem card_le_card_pow (hn : n ≠ 0) : #s ≤ #(s ^ n) := by
  simpa using Finset.card_pow_mono (s := s) one_ne_zero (Nat.one_le_iff_ne_zero.2 hn)

