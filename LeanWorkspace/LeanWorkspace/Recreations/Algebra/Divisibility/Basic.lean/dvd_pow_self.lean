import Mathlib

variable {α : Type*}

variable [Monoid α] {a b c : α} {m n : ℕ}

theorem dvd_pow_self (a : α) {n : ℕ} (hn : n ≠ 0) : a ∣ a ^ n := dvd_rfl.pow hn

