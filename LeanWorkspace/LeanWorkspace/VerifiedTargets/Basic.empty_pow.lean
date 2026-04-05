import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem empty_pow (hn : n ≠ 0) : (∅ : Finset α) ^ n = ∅ := match n with | n + 1 => by simp [pow_succ]

