import Mathlib

variable {F α β γ : Type*}

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

theorem empty_pow (hn : n ≠ 0) : (∅ : Set α) ^ n = ∅ := match n with | n + 1 => by simp [pow_succ]

