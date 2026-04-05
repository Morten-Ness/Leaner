import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem card_pow_le : ∀ {n}, #(s ^ n) ≤ #s ^ n
  | 0 => by simp
  | n + 1 => by rw [pow_succ, pow_succ]; refine Finset.card_mul_le.trans (by gcongr; exact card_pow_le)
