import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [CancelMonoid α] {s : Finset α} {m n : ℕ}

theorem card_pow_mono (hm : m ≠ 0) (hmn : m ≤ n) : #(s ^ m) ≤ #(s ^ n) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [hm]
  · exact hs.card_pow_mono hmn

